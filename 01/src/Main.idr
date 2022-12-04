module Main

import Control.App
import Control.App.Console
import Control.App.FileIO
import Control.Monad.Trans
import Data.Nat
import Data.String
import System.File.Virtual


-- Halting problem go brrr...
%default total


--data Consumer : (history: List Nat) -> a -> Type where
--    Return : (0 history: List Nat) -> a -> Consumer history a
--    Consume : (0 history: List Nat) -> ((x: Nat) -> Consumer (x :: history) a) -> Consumer history a
--
--
--Functor (Consumer history) where
--    map f c = recurse history c where
--        recurse : (0 history: List Nat) -> Consumer history a -> Consumer history b
--        recurse history (Return history x) = Return history (f x)
--        recurse history (Consume history next) = Consume history (\x => recurse (x :: history) (next x))
--
--
--Applicative (Consumer history) where
--    pure = Return history
--    fn <*> arg = recurse history fn where
--        recurse : (0 history: List Nat) -> Consumer history (a -> b) -> Consumer history b
--        recurse history (Return history x) = map x arg
--        recurse history (Consume history next) = Consume history (\x => recurse (x :: history) (next x))
--
--
--myConsumer : (0 history: List Nat) -> Consumer history Nat
--myConsumer history = Consume history $ \x => Return (x :: history) x
--
--otherConsumer : (0 history: List Nat) -> Consumer history Nat
--otherConsumer history = Return history 3
--
--combinedConsumer : (0 history: List Nat) -> Consumer history Nat
--combinedConsumer history = mybind (myConsumer history)  (\x, newHistory => otherConsumer newHistory) where
--    mybind : Consumer history Nat ->  (Nat -> (newHistory: List Nat) -> Consumer newHistory Nat) -> Consumer history Nat


-- Pipe implementation ported from Idris v1 to Idris v2 based on QuentinDuval/IdrisPipes
-- Extensions to IdrisPipes: We now index by history (erased at runtime) so we can reason
-- about some properties of what a pipe outputs.
data Pipe :
    (streamIn, streamOut, returnIn: Type)
    -> {0 history : List streamIn}
    -> (effects : Type -> Type)
    -> (returnOut : Type) -> Type where
    Do :
        {0 history : List streamIn}
        -> effects (Inf (Pipe streamIn streamOut returnIn {history = history} effects returnOut))
        -> Pipe streamIn streamOut returnIn {history = history} effects returnOut
    Yield :
        {0 history : List streamIn}
        -> Inf (Pipe streamIn streamOut returnIn {history = history} effects returnOut)
        -> streamOut
        -> Pipe streamIn streamOut returnIn {history = history} effects returnOut
    Await :
        {0 history : List streamIn}
        -> (returnIn -> Inf (Pipe streamIn streamOut returnIn {history = history} effects returnOut))
        -> ((value: streamIn) -> Inf (Pipe
            streamIn
            streamOut
            returnIn
            {history = (value :: history)}
            effects
            returnOut))
        -> Pipe streamIn streamOut returnIn {history = history} effects returnOut
    Return :
        {0 history : List streamIn}
        -> returnOut
        -> Pipe streamIn streamOut returnIn {history = history} effects returnOut


||| Idris's type inference has a very hard time figuring this one out, so we explicitly type it
||| instead of using `pure` directly.
lazyPure :
    Monad effects
    => {0 streamIn: Type}
    -> {0 history: List streamIn}
    -> Inf (Pipe streamIn streamOut returnIn {history = history} effects returnOut)
    -> effects (Inf (Pipe streamIn streamOut returnIn {history = history} effects returnOut))
lazyPure = pure


partial
recurseToReturn :
    Monad effects
    => {0 streamIn: Type}
    -> {0 history: List streamIn}
    -> Pipe streamIn streamOut returnIn {history = history} effects a
    -> ((0 mapHistory: List streamIn)
        -> a
        -> Pipe streamIn streamOut returnIn {history = mapHistory} effects b)
    -> Pipe streamIn streamOut returnIn {history = history} effects b
recurseToReturn pipe mapReturn = recurse {history = history} pipe where
    recurse :
        {0 history: List streamIn}
        -> Pipe streamIn streamOut returnIn {history = history} effects a
        -> Pipe streamIn streamOut returnIn {history = history} effects b
    recurse {history} (Do {history = history} action) = Do
        {history = history}
        (do
            next <- action
            lazyPure
                {streamIn = streamIn}
                {history = history}
                (recurse {history = history} next)
        )
    recurse {history} (Yield next value) = Yield {history = history} (recurse {history = history} next) value
    recurse {history} (Await onReturn onStream) = Await
        {history = history}
        (\end => recurse {history = history} (onReturn end))
        (\streamNext => recurse {history = (streamNext :: history)} (onStream streamNext))
    recurse {history} (Return value) = mapReturn history value


Monad effects
=> Functor (Pipe streamIn streamOut returnIn {history} effects) where
    map function pipe = assert_total
        recurseToReturn pipe mapReturnWithFunction where
            mapReturnWithFunction:
                (0 mapHistory: List streamIn)
                -> a
                -> Pipe streamIn streamOut returnIn {history = mapHistory} effects b
            mapReturnWithFunction mapHistory value = Return {history = mapHistory} (function value)

        --recurseToReturn streamIn history pipe mapReturnWithFunction where
        --    mapReturnWithFunction:
        --        {auto 0 mapHistory: List streamIn}
        --        -> a
        --        -> Pipe streamIn streamOut returnIn {history = mapHistory} effects b
        --    mapReturnWithFunction value = Return {history = mapHistory} (function value)


-- Monad effects => Applicative (Pipe streamIn streamOut returnIn {history=wat} effects) where
--    pure = Return
--    pipeFunction <*> pipeArgument = assert_total
--        recurseToReturn pipeFunction mapReturnWithArgument where
--            mapReturnWithArgument:
--                (0 mapHistory: List streamIn)
--                -> x
--                -> Pipe streamIn streamOut returnIn {history = mapHistory} effects y
--            mapReturnWithArgument mapHistory value = map ?valueTodo pipeArgument


-- Monad effects => Monad (Pipe streamIn streamOut returnIn effects) where
--     effects >>= function = assert_total
--         recurseToReturn effects (\value => function value)


partial
(>>=) :
    Monad effects
    =>
    --{0 streamIn: Type}
    ---> {0 history: List streamIn}
    Pipe streamIn streamOut returnIn {history} effects returnMid
    -- -> (returnMid -> Pipe streamIn streamOut returnIn effects returnOut)
    -> (returnMid -> {0 newHistory: List streamIn} -> Pipe streamIn streamOut returnIn {history = newHistory} effects returnOut)
    -> Pipe streamIn streamOut returnIn {history} effects returnOut
effects >>= function = recurseToReturn effects (\mapHistory, value => function value)


-- MonadTrans (Pipe streamIn streamOut returnIn) where
--     lift effects = Do (effects >>= \value => lazyPure (Return value))


lift :
    Monad effects
    => effects returnOut
    -> Pipe streamIn streamOut returnIn {history} effects returnOut
lift effects = Do (effects >>= \value => lazyPure (Return value))


infixr 9 .|
||| The pipe operator chains two pipes together.
partial --todo totality
(.|) :
    Monad effects
    => --{0 streamIn: Type}
    ---> {0 streamMid: Type}
    ---> {0 historyIn: List streamIn}
    ---> {0 historyMid: List streamMid}
     Pipe streamIn streamMid returnIn {history = historyIn} effects returnMid
    -> Pipe streamMid streamOut returnMid {history = historyMid} effects returnOut
    -> Pipe streamIn streamOut returnIn {history = historyIn} effects returnOut
(.|) = pull where
    mutual
        pull : 
            Monad effects'
            =>
            --{0 streamIn: Type}
            ---> {0 streamMid: Type}
             {0 pullHistoryIn: List streamIn}
            -> {0 pullHistoryMid: List streamMid}
            -> Pipe streamIn streamMid returnIn {history = pullHistoryIn} effects' returnMid
            -> Pipe streamMid streamOut returnMid {history = pullHistoryMid} effects' returnOut
            -> Pipe streamIn streamOut returnIn {history = pullHistoryIn} effects' returnOut
        pull upstream (Do action)
            --= Do
            --(do
            --    downstreamNext <- action
            --    pull
            --)
            --= lift action >>= \next => pull ?todoupstream ?todopullnext--next

            --= lift action >>= ?todopullnext where
            --    -- Downstream doesn't affect pullHistoryIn at all, although pullHistoryMid may have changed
            --    next :
            --        Inf (Pipe streamMid streamOut returnMid {history = newPullHistoryMid} effects' returnOut)
            --        -> Pipe streamIn streamOut returnIn {history = pullHistoryIn} effects' returnOut
            --    next nextPipe = pull {pullHistoryIn = pullHistoryIn} upstream nextPipe

            --= recurseToReturn
            --    (lift action)
            --    -- Problem: mapHistory should stay the same as pullHistoryIn because upstream hasn't pulled, but
            --    -- downstream may have pulled and therefore pullHistoryIn may have changed, but
            --    -- we don't know what it changed to.
            --    (\mapHistory, nextPipe => ?todopullrecurse
            --        --pull
            --        --    {pullHistoryIn = pullHistoryIn}
            --        --    {pullHistoryMid = mapHistory}
            --        --    upstream
            --        --    nextPipe
            --    )

            --= Do (effects >>= \value => )
            --= Do
                --(do
                --    nextDownstreamPipe <- action
                --    lazyPure (pull upstream nextDownstreamPipe)
                --)
            = Do (action >>= \nextDownstreamPipe => lazyPure (pull upstream nextDownstreamPipe))
        pull upstream (Yield downstreamNext value)
            = Yield (pull upstream downstreamNext) value
        pull upstream (Await downstreamOnReturn downstreamOnStream)
            = push upstream downstreamOnReturn downstreamOnStream
        pull upstream (Return value)
            = Return value

        push :
            Monad effects'
            => {0 streamIn: Type}
            -> {0 streamMid: Type}
            -> {0 historyIn: List streamIn}
            -> {0 historyMid: List streamMid}
            -> Pipe streamIn streamMid returnIn {history = historyIn} effects' returnMid
            -> (returnMid -> Inf (Pipe streamMid streamOut returnMid {history = historyMid} effects' returnOut))
            -> ((value: streamMid) -> Inf (Pipe streamMid streamOut returnMid {history = value :: historyMid} effects' returnOut))
            -> Pipe streamIn streamOut returnIn {history = historyIn} effects' returnOut
        push (Do action) downstreamOnReturn downstreamOnStream
            = lift action >>= \next => push ?todonext downstreamOnReturn downstreamOnStream
        push (Yield upstreamNext value) downstreamOnReturn downstreamOnStream
            = pull upstreamNext (downstreamOnStream value)
        push (Await upstreamOnReturn upstreamOnStream) downstreamOnReturn downstreamOnStream
            = Await
                (\value => push (upstreamOnReturn value) downstreamOnReturn downstreamOnStream)
                (\value => push (upstreamOnStream value) downstreamOnReturn downstreamOnStream)
        push (Return value) downstreamOnReturn downstreamOnStream
            = pull (Return value) (downstreamOnReturn value)


yield : streamOut -> Pipe streamIn streamOut returnIn effects ()
yield value = Yield (Return ()) value -- We set Return () as the initial continuation, which can then be built upon monadically


Effect : (effects: Type -> Type) -> (return: Type) -> Type
Effect effects return = Pipe Void Void Void {history = []} effects return


partial
runPipe : Monad effects => Effect effects return -> effects return
runPipe (Do action) = action >>= \nextPipe => runPipe nextPipe
runPipe (Yield _ value) = absurd value
runPipe (Await _ _) = runPipe $ Await absurd (\x => absurd x)
runPipe (Return value) = pure value 


namespace DoNotationWithoutMonadsBigQuestionMark
    data Lol a = Hahahaha a | Boooo
    (>>=) : Lol a -> (a -> Lol b) -> Lol b

    x : Lol String
    x = do
        test <- (Hahahaha 3)
        test2 <- (Hahahaha (test * 2))
        Boooo


partial
mapEach : Monad effects => (streamIn -> streamOut) -> Pipe streamIn streamOut return effects return
mapEach function = Await  
    (\returnValue => Return returnValue)
    (\streamValue => do
        _ <- yield (function streamValue)
        mapEach function
    )


foldPipe :
    (reducer: streamIn -> returnOut -> returnOut)
    -> (initialValue: returnOut)
    -> Pipe streamIn Void () effects returnOut
foldPipe reducer accumulator = Await
    (\_ => Return accumulator)
    (\streamValue => foldPipe reducer (reducer streamValue accumulator))



partial
readLines : Has [FileIO, Console] effects => Pipe Void String Void {history = []} (App effects) ()
readLines = recurse where
    recurse : Pipe Void String Void (App effects) ()
    recurse = do
        _ <- lift $ putStrLn "Reading next line..."
        -- TODO: Does this skip the last line?
        line <- lift getLine
        eof <- lift $ fEOF stdin
        if eof
            then Return ()
            else do
                _ <- yield line
                recurse


partial
printEach :
    (Show streamValue, Has [Console] effects)
    => Pipe streamValue streamValue () {history = []} (App effects) ()
printEach = recurse where
    recurse : Pipe streamValue streamValue () (App effects) ()
    recurse = Await
        (\_ => Return ())
        (\streamValue => do
            _ <- lift $ putStrLn "Printing..."
            _ <- lift $ putStrLn (show streamValue)
            _ <- yield streamValue
            recurse
        )


partial
splitByEmptyLine :
    Monad effects
    => Pipe String Void () effects splitReturnOut
    -> Pipe String splitReturnOut () {history = []} effects ()
splitByEmptyLine initialInnerPipeline = runInnerPipe False initialInnerPipeline where
    runInnerPipe :
        (hasEnded: Bool)
        -> Pipe String Void () effects splitReturnOut
        -> Pipe String splitReturnOut () effects ()
    runInnerPipe hasEnded (Do action) = do
        nextPipe <- lift action
        runInnerPipe hasEnded ?nextPipe
    runInnerPipe _ (Yield _ value) = absurd value
    runInnerPipe _ (Await onReturn onStream) =
        Await
            (\_ => runInnerPipe True (onReturn ()))
            (\streamValue => case streamValue of
                "" => runInnerPipe False (onReturn ())
                nonEmpty => runInnerPipe False (onStream nonEmpty))
    runInnerPipe hasEnded (Return value) = do
        _ <- yield value
        if hasEnded
            then Return ()
            else runInnerPipe False initialInnerPipeline


partial
parseNat : Monad effects => Pipe String Nat return {history = []} effects return
parseNat = mapEach stringToNatOrZ


sum : Pipe Nat Void () {history = []} effects Nat
sum = foldPipe (+) 0


max : Pipe Nat Void () {history = []} effects Nat
max = foldPipe maximum 0


printReturnValue :
    (Show return, Has [Console] effects) => Pipe Void Void return {history = []} (App effects) ()
printReturnValue = recurse where
    recurse : Pipe Void Void return (App effects) ()
    recurse = Await
        (\returnValue => lift $ putStrLn (show returnValue))
        (\_ => recurse)


partial
app : Has [FileIO, Console] effects => App effects ()
app = runPipe $
    readLines
    .| splitByEmptyLine (parseNat .| printEach .| sum)
    .| printEach
    .| max
    .| printReturnValue


partial
main : IO ()
main = run $ handle app
    (\() => putStr "Ok")
    (\error : IOError => putStr "Error")