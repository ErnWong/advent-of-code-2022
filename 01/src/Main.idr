module Main

--import Control.App
--import Control.App.Console
--import Control.App.FileIO
import Control.Monad.Trans
import Data.Colist
import System.File.Virtual
import System.File.ReadWrite


-- Halting problem go brrr...
%default total


-- Pipe implementation ported from Idris v1 to Idris v2 based on QuentinDuval/IdrisPipes
data Pipe :
    (streamIn, streamOut, returnIn: Type)
    -> (effects : Type -> Type)
    -> (returnOut : Type) -> Type where
    Do :
        effects (Inf (Pipe streamIn streamOut returnIn effects returnOut))
        -> Pipe streamIn streamOut returnIn effects returnOut
    Yield :
        Inf (Pipe streamIn streamOut returnIn effects returnOut)
        -> streamOut
        -> Pipe streamIn streamOut returnIn effects returnOut
    Await :
        (Either returnIn streamIn -> Inf (Pipe streamIn streamOut returnIn effects returnOut))
        -> Pipe streamIn streamOut returnIn effects returnOut
    Return :
        returnOut
        -> Pipe streamIn streamOut returnIn effects returnOut

--    data Pipe : (returnOut : Type) -> Type where
--        Do' :
--            effects (Inf (Pipe returnOut))
--            -> Pipe returnOut
--        Yield' :
--            Inf (Pipe returnOut)
--            -> streamOut
--            -> Pipe returnOut
--        Await' :
--            (Either returnIn streamIn -> Inf (Pipe returnOut))
--            -> Pipe returnOut
--        Return' :
--            returnOut
--            -> Pipe returnOut


--Why can't I get parameters and interface implementations to work nicely?!
-- --parameters {effects : Type -> Type} {streamIn: Type} {streamOut: Type} {returnIn: Type}
-- -- Btw these parameters blocks are very nice!
-- parameters (effects : Type -> Type) (streamIn: Type) (streamOut: Type) (returnIn: Type)
-- 
--     ||| It'll be convenient to not type out all the parameters everytime, so
--     ||| here's a type alias for `Pipe`
--     Pipe' : Type -> Type
--     Pipe' returnOut = Pipe streamIn streamOut returnIn effects returnOut
-- 
-- 
--     ||| Idris's type inference has a very hard time figuring this one out, so we explicitly type it
--     ||| instead of using `pure` directly.
--     lazyPure : (Monad effects) => Inf (Pipe' b) -> effects (Inf (Pipe' b))
--     lazyPure = pure
-- 
-- 
--     partial
--     recurseToReturn : (Monad effects) => Pipe' a -> (mapReturn: a -> Pipe' b) -> Pipe' b
--     recurseToReturn pipe mapReturn = recurse pipe where
--         recurse : Pipe' a -> Pipe' b
--         -- Dear reader...
--         --   I want to apologize
--         --    for what follows....
--         --
--         --recurse (Do action) =
--         --    let
--         --        0 lazyPipe = Inf (Pipe' b)
--         --        lazyPure = the (lazyPipe -> effects lazyPipe) pure
--         --    in
--         --        -- Do (action >>= \next : Inf (Pipe' a)
--         --        Do (action >>= \next => lazyPure (recurse next))
--         --recurse (Do action) = Do (do
--         --    next <- action
--         --    let x = recurse next
--         --    --let y = the (effects (Inf (Pipe' b))) ((the ((Pipe' b) -> (effects (Pipe' b))) pure) x)
--         --    -- For some reason, idris can't infer that pure takes an Inf value...
--         --    let y = (the (Inf (Pipe' b) -> (effects (Inf (Pipe' b)))) pure) x
--         --    --let z = pure x
--         --    --let zz = the (effects _) (pure (the (Inf _) (Delay x)))
--         --    --?todo)
--         --    y)
--         --    pure (recurse next))
--         --recurse (Do action) = ?todo
--         recurse (Do action) = Do (do
--             next <- action
--             -- let 0 thePipe = Pipe' b
--             -- let 0 lazyPipe = Inf (Pipe' b)
--             -- let lazyPure = the (lazyPipe -> effects lazyPipe) pure
--             -- let lazyPure = the (Inf thePipe -> effects (Inf thePipe)) pure
--             -- let lazyPure = the (Inf (thePipe) -> (effects (Inf (thePipe)))) pure
--             -- let lazyPure_result = (the (Inf (Pipe' b) -> (effects (Inf (Pipe' b)))) pure) x
--             -- let lazyPure = (the lazyPipe -> (effects (Inf (Pipe' b)))) pure)
--             --
--             -- heeeeeeelllllllppppppp
--             -- No idea why this works by the others don't...
--             -- but for some reason, idris really wants `pure` to be eager, so we are explicit
--             -- about the laziness here. Don't know why creating a type alias doesn't work.
--             -- Finally, this works...
--             --let lazyPure = the (Inf (Pipe' b) -> (effects (Inf (Pipe' b)))) pure
--             lazyPure (recurse next))
--         recurse (Yield next value) = Yield (recurse next) value
--         recurse (Await continuation) = Await (\next => recurse (continuation next))
--         recurse (Return value) = mapReturn value
--             --let x = mapReturn ?wat
--             --in ?valuetodo--mapReturn value
-- 
-- 
--     [PipeFunctor] (Monad effects) => Functor Pipe' where
--         map function pipe = assert_total recurseToReturn pipe (\value => Return (function value))
-- 
--     --implementation (Monad effects) => Functor (Pipe streamIn streamOut returnIn effects) where
--     --    map function pipe = assert_total recurseToReturn pipe (\value => Return (function value))
-- 
--     implementation (Monad effects) => Applicative Pipe' using PipeFunctor where
--         pure = Return
--         pipeFunction <*> pipeArgument = assert_total recurseToReturn pipeFunction (\value => map value pipeArgument)
-- 
-- 
--     --implementation (Monad effects) => Monad Pipe' where
--     --    effects >>= function = assert_total recurseToReturn effects (\value => function value)

||| Idris's type inference has a very hard time figuring this one out, so we explicitly type it
||| instead of using `pure` directly.
lazyPure :
    (Monad effects)
    => Inf (Pipe streamIn streamOut returnIn effects returnOut)
    -> effects (Inf (Pipe streamIn streamOut returnIn effects returnOut))
lazyPure = pure


partial
recurseToReturn :
    (Monad effects)
    => Pipe streamIn streamOut returnIn effects a
    -> (mapReturn: a -> Pipe streamIn streamOut returnIn effects b)
    -> Pipe streamIn streamOut returnIn effects b
recurseToReturn pipe mapReturn = recurse pipe where
    recurse :
        Pipe streamIn streamOut returnIn effects a
        -> Pipe streamIn streamOut returnIn effects b
    -- Dear reader...
    --   I want to apologize
    --    for what follows....
    --
    --recurse (Do action) =
    --    let
    --        0 lazyPipe = Inf (Pipe' b)
    --        lazyPure = the (lazyPipe -> effects lazyPipe) pure
    --    in
    --        -- Do (action >>= \next : Inf (Pipe' a)
    --        Do (action >>= \next => lazyPure (recurse next))
    --recurse (Do action) = Do (do
    --    next <- action
    --    let x = recurse next
    --    --let y = the (effects (Inf (Pipe' b))) ((the ((Pipe' b) -> (effects (Pipe' b))) pure) x)
    --    -- For some reason, idris can't infer that pure takes an Inf value...
    --    let y = (the (Inf (Pipe' b) -> (effects (Inf (Pipe' b)))) pure) x
    --    --let z = pure x
    --    --let zz = the (effects _) (pure (the (Inf _) (Delay x)))
    --    --?todo)
    --    y)
    --    pure (recurse next))
    --recurse (Do action) = ?todo
    recurse (Do action) = Do (do
        next <- action
        -- let 0 thePipe = Pipe' b
        -- let 0 lazyPipe = Inf (Pipe' b)
        -- let lazyPure = the (lazyPipe -> effects lazyPipe) pure
        -- let lazyPure = the (Inf thePipe -> effects (Inf thePipe)) pure
        -- let lazyPure = the (Inf (thePipe) -> (effects (Inf (thePipe)))) pure
        -- let lazyPure_result = (the (Inf (Pipe' b) -> (effects (Inf (Pipe' b)))) pure) x
        -- let lazyPure = (the lazyPipe -> (effects (Inf (Pipe' b)))) pure)
        --
        -- heeeeeeelllllllppppppp
        -- No idea why this works by the others don't...
        -- but for some reason, idris really wants `pure` to be eager, so we are explicit
        -- about the laziness here. Don't know why creating a type alias doesn't work.
        -- Finally, this works...
        --let lazyPure = the (Inf (Pipe' b) -> (effects (Inf (Pipe' b)))) pure
        lazyPure (recurse next))
    recurse (Yield next value) = Yield (recurse next) value
    recurse (Await continuation) = Await (\next => recurse (continuation next))
    recurse (Return value) = mapReturn value
        --let x = mapReturn ?wat
        --in ?valuetodo--mapReturn value


(Monad effects) => Functor (Pipe streamIn streamOut returnIn effects) where
    map function pipe = assert_total recurseToReturn pipe (\value => Return (function value))


(Monad effects) => Applicative (Pipe streamIn streamOut returnIn effects) where
    pure = Return
    pipeFunction <*> pipeArgument = assert_total recurseToReturn pipeFunction (\value => map value pipeArgument)


(Monad effects) => Monad (Pipe streamIn streamOut returnIn effects) where
    effects >>= function = assert_total recurseToReturn effects (\value => function value)


MonadTrans (Pipe streamIn streamOut returnIn) where
    lift effects = Do (effects >>= \value => lazyPure (Return value))


infixr 9 .|
||| The pipe operator chains two pipes together.
partial --todo totality
(.|) :
    (Monad effects)
    => Pipe streamIn streamMid returnIn effects returnMid
    -> Pipe streamMid streamOut returnMid effects returnOut
    -> Pipe streamIn streamOut returnIn effects returnOut
(.|) = pull where
    mutual
        pull : 
            (Monad effects')
            => Pipe streamIn streamMid returnIn effects' returnMid
            -> Pipe streamMid streamOut returnMid effects' returnOut
            -> Pipe streamIn streamOut returnIn effects' returnOut
        pull upstream (Do action)
            = lift action >>= \next => pull upstream next
        pull upstream (Yield downstreamNext value)
            = Yield (pull upstream downstreamNext) value
        pull upstream (Await downstreamContinuation)
            = push upstream downstreamContinuation
        pull upstream (Return value)
            = Return value

        push :
            (Monad effects')
            => Pipe streamIn streamMid returnIn effects' returnMid
            -> (Either returnMid streamMid -> Inf (Pipe streamMid streamOut returnMid effects' returnOut))
            -> Pipe streamIn streamOut returnIn effects' returnOut
        push (Do action) downstream
            = lift action >>= \next => push next downstream
        push (Yield upstreamNext value) downstream
            = pull upstreamNext (downstream (Right value))
        push (Await upstreamContinuation) downstream
            = Await (\value => push (upstreamContinuation value) downstream)
        push (Return value) downstream
            = pull (Return value) (downstream (Left value))


Effect : (effects: Type -> Type) -> (return: Type) -> Type
Effect effects return = Pipe Void Void Void effects return


partial
runPipe : (Monad effects) => Effect effects return -> effects return
runPipe (Do action) = action >>= \nextPipe => runPipe nextPipe
runPipe (Yield _ value) = absurd value
runPipe (Await _ ) = runPipe $ Await (either absurd absurd)
runPipe (Return value) = pure value 


partial
readLinesPipe : Pipe Void String Void IO ()
readLinesPipe = do
    lift $ putStrLn "Reading next line..."
    -- TODO: Does this skip the last line?
    line <- lift getLine
    eof <- lift $ fEOF stdin
    if eof
        then Return ()
        else do
            Yield (Return ()) line -- Pure () doesn't seem right - don't we want to be the continuation?
            readLinesPipe

partial
printLinesPipe : Pipe String Void () IO ()
printLinesPipe = do
    Await $ \next => case next of
        Right value => do
            lift $ putStrLn "Printing..."
            lift $ putStrLn value
            printLinesPipe
        _ => Return ()

partial
main : IO ()
main = runPipe $ readLinesPipe .| printLinesPipe

--partial
--readLines : Has [FileIO, Console] effects => App effects (Colist String)
--readLines = do
--    putStrLn "Reading next line..."
--    -- TODO: Does this skip the last line?
--    line <- getLine
--    eof <- fEOF stdin
--    if eof
--        then pure []
--        else do
--            rest <- readLines
--            pure (line :: rest)
--
--
--data Elves : List String -> Type where
--
--
---- split : List a -> (a -> Bool) -> List (List a)
---- split list isDelimiter = split' list isDelimiter []
----     where
----         split' [] _ accumulator = accumulator
----         split'(x :: xs) isDelimiter accumulator =
----             if isDelimiter x
----             then (split' xs []) :: (reverse accumulator
--
--
--partial
--printLines : Has [Console] effects => Colist String -> App effects ()
--printLines [] = putStrLn "Done"
--printLines (line :: rest) = do
--    putStrLn $ "Line: " ++ line
--    printLines rest
--
--
--partial
--main : IO ()
--main = run $ handle (readLines >>= printLines)
--    (\() => putStr "Ok")
--    (\error : IOError => putStr "Error")
--