module Main

import Control.App
import Control.App.Console
import Control.App.FileIO
import Control.Monad.Trans
import Data.Colist
import System.File.Virtual


-- Halting problem go brrr...
%default total


||| Pipe implementation ported from Idris v1 to Idris v2 based on QuentinDuval/IdrisPipes

data Pipe :
    (effects : Type -> Type)
    -> (streamIn, streamOut, returnIn: Type)
    -> (returnOut : Type)
    -> Type where
    Do :
        effects (Inf (Pipe effects streamIn streamOut returnIn returnOut))
        -> Pipe effects streamIn streamOut returnIn returnOut
    Yield :
        Inf (Pipe effects streamIn streamOut returnIn returnOut)
        -> streamOut
        -> Pipe effects streamIn streamOut returnIn returnOut
    Await :
        (Either returnIn streamIn -> Inf (Pipe effects streamIn streamOut returnIn returnOut))
        -> Pipe effects streamIn streamOut returnIn returnOut
    Return :
       returnOut
       -> Pipe effects streamIn streamOut returnIn returnOut


implementation (Monad effects) => Functor (Pipe effects streamIn streamOut returnIn) where
    map f p = assert_total recurse (Delay p) where
        partial
        recurse :
            Inf (Pipe effects streamIn streamOut returnIn a)
            -> Pipe effects streamIn streamOut returnIn b
        -- Dear reader...
        --   I want to apologize
        --    for what follows....
        --
        --recurse (Do action) =
        --    let
        --        0 lazy_pipe = Inf (Pipe effects streamIn streamOut returnIn b)
        --        lazy_pure = the (lazy_pipe -> effects lazy_pipe) pure
        --    in
        --        -- Do (action >>= \next : Inf (Pipe effects streamIn streamOut returnIn a)
        --        Do (action >>= \next => lazy_pure (recurse next))
        --recurse (Do action) = Do (do
        --    next <- action
        --    let x = recurse next
        --    --let y = the (effects (Inf (Pipe effects streamIn streamOut returnIn b))) ((the ((Pipe effects streamIn streamOut returnIn b) -> (effects (Pipe effects streamIn streamOut returnIn b))) pure) x)
        --    -- For some reason, idris can't infer that pure takes an Inf value...
        --    let y = (the (Inf (Pipe effects streamIn streamOut returnIn b) -> (effects (Inf (Pipe effects streamIn streamOut returnIn b)))) pure) x
        --    --let z = pure x
        --    --let zz = the (effects _) (pure (the (Inf _) (Delay x)))
        --    --?todo)
        --    y)
        --    pure (recurse next))
        --recurse (Do action) = ?todo
        recurse (Do action) = Do (do
            next <- action
            let 0 the_pipe = Pipe effects streamIn streamOut returnIn b
            -- let 0 lazy_pipe = Inf (Pipe effects streamIn streamOut returnIn b)
            -- let lazy_pure = the (lazy_pipe -> effects lazy_pipe) pure
            -- let lazy_pure = the (Inf the_pipe -> effects (Inf the_pipe)) pure
            -- let lazy_pure = the (Inf (the_pipe) -> (effects (Inf (the_pipe)))) pure
            -- let lazy_pure_result = (the (Inf (Pipe effects streamIn streamOut returnIn b) -> (effects (Inf (Pipe effects streamIn streamOut returnIn b)))) pure) x
            -- let lazy_pure = (the lazy_pipe -> (effects (Inf (Pipe effects streamIn streamOut returnIn b)))) pure)
            --
            -- heeeeeeelllllllppppppp
            -- No idea why this works by the others don't...
            -- but for some reason, idris really wants `pure` to be eager, so we are explicit
            -- about the laziness here. Don't know why creating a type alias doesn't work.
            let lazy_pure = the (Inf (Pipe effects streamIn streamOut returnIn b) -> (effects (Inf (Pipe effects streamIn streamOut returnIn b)))) pure
            lazy_pure (recurse next))
        recurse (Yield next value) = Yield (recurse next) value
        recurse (Await continuation) = Await (\next => recurse (continuation next))
        recurse (Return value) = Return (f value)


implementation (Monad effects) => Applicative (Pipe effects streamIn streamOut returnIn) where
    pure = Return
    pipeFunction <*> pipeArgument = (recurse pipeFunction) where
        recurse : 
        recurse (Do action) = Action (a >>= \next => pure (recurse next))
        recurse (Yield next value) = Yield (recurse next) value
        recurse (Await continuation) = Await (\next => recurse (continuation next))
        recurse (Return value) = map value pipeArgument


||| The pipe operator chains two pipes together.
partial --todo totality
(.|) :
    (Monad effects)
    => Pipe effects streamIn streamMid returnIn returnMid
    -> Pipe effects streamMid streamOut returnMid returnOut
    -> Pipe effects streamIn streamOut returnIn returnOut
(.|) = pull where
    mutual
        pull : 
            (Monad effects')
            => Pipe effects' streamIn streamMid returnIn returnMid
            -> Pipe effects' streamMid streamOut returnMid returnOut
            -> Pipe effects' streamIn streamOut returnIn returnOut
        pull upstream (Do action)
            = ?todopull --lift action >>= \next => pull upstream next
        pull upstream (Yield downstreamNext value)
            = Yield (pull upstream downstreamNext) value
        pull upstream (Await downstreamContinuation)
            = ?todopullawait-- push upstream downstreamContinuation
        pull upstream (Return value)
            = Return value

        push :
            (Monad effects')
            => Pipe effects' streamIn streamMid returnIn returnMid
            -> (Either returnMid streamMid -> Pipe effects' streamMid streamOut returnMid returnOut)
            -> Pipe effects' streamIn streamOut returnIn returnOut
        push (Do action) downstream
            = ?todopushdo-- lift action >>= \next => pull next downstream
        push (Yield upstreamNext value) downstream
            = pull upstreamNext (downstream (Right value))
        push (Await upstreamContinuation) downstream
            = Await (\value => push (upstreamContinuation value) downstream)
        push (Return value) downstream
            = pull (Return value) (downstream (Left value))


Effect : (effects: Type -> Type) -> (return: Type) -> Type
Effect effects return = Pipe effects Void Void Void return


partial
runPipe : (Monad effects) => Effect effects return -> effects return
runPipe (Do action) = action >>= \nextPipe => runPipe nextPipe
runPipe (Yield _ value) = absurd value
runPipe (Await _ ) = runPipe $ Await (either absurd absurd)
runPipe (Return value) = pure value 


partial
readLines : Has [FileIO, Console] effects => App effects (Colist String)
readLines = do
    putStrLn "Reading next line..."
    -- TODO: Does this skip the last line?
    line <- getLine
    eof <- fEOF stdin
    if eof
        then pure []
        else do
            rest <- readLines
            pure (line :: rest)


data Elves : List String -> Type where


-- split : List a -> (a -> Bool) -> List (List a)
-- split list isDelimiter = split' list isDelimiter []
--     where
--         split' [] _ accumulator = accumulator
--         split'(x :: xs) isDelimiter accumulator =
--             if isDelimiter x
--             then (split' xs []) :: (reverse accumulator


partial
printLines : Has [Console] effects => Colist String -> App effects ()
printLines [] = putStrLn "Done"
printLines (line :: rest) = do
    putStrLn $ "Line: " ++ line
    printLines rest


partial
main : IO ()
main = run $ handle (readLines >>= printLines)
    (\() => putStr "Ok")
    (\error : IOError => putStr "Error")
