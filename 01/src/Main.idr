module Main

--import Control.App
--import Control.App.Console
--import Control.App.FileIO
import Control.Monad.Trans
import Data.Nat
import Data.String
import System.File.Virtual


-- Halting problem go brrr...
%default total


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
            {history = value :: history}
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
        (\streamNext => recurse {history = streamNext :: history} (onStream streamNext))
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


Monad effects => Applicative (Pipe streamIn streamOut returnIn {history} effects) where
    pure = Return
    pipeFunction <*> pipeArgument = assert_total
        recurseToReturn pipeFunction mapReturnWithArgument where
            mapReturnWithArgument:
                (0 mapHistory: List streamIn)
                -> x
                -> Pipe streamIn streamOut returnIn {history = mapHistory} effects y
            mapReturnWithArgument mapHistory value = ?todo--map ?valueTodo pipeArgument


--Monad effects => Monad (Pipe streamIn streamOut returnIn effects) where
--    effects >>= function = assert_total
--        recurseToReturn effects (\value => function value)
--
--
--MonadTrans (Pipe streamIn streamOut returnIn) where
--    lift effects = Do (effects >>= \value => lazyPure (Return value))


--infixr 9 .|
--||| The pipe operator chains two pipes together.
--partial --todo totality
--(.|) :
--    Monad effects
--    => Pipe streamIn streamMid returnIn effects returnMid
--    -> Pipe streamMid streamOut returnMid effects returnOut
--    -> Pipe streamIn streamOut returnIn effects returnOut
--(.|) = pull where
--    mutual
--        pull : 
--            Monad effects'
--            => Pipe streamIn streamMid returnIn effects' returnMid
--            -> Pipe streamMid streamOut returnMid effects' returnOut
--            -> Pipe streamIn streamOut returnIn effects' returnOut
--        pull upstream (Do action)
--            = lift action >>= \next => pull upstream next
--        pull upstream (Yield downstreamNext value)
--            = Yield (pull upstream downstreamNext) value
--        pull upstream (Await downstreamContinuation)
--            = push upstream downstreamContinuation
--        pull upstream (Return value)
--            = Return value
--
--        push :
--            Monad effects'
--            => Pipe streamIn streamMid returnIn effects' returnMid
--            -> (Either returnMid streamMid -> Inf (Pipe streamMid streamOut returnMid effects' returnOut))
--            -> Pipe streamIn streamOut returnIn effects' returnOut
--        push (Do action) downstream
--            = lift action >>= \next => push next downstream
--        push (Yield upstreamNext value) downstream
--            = pull upstreamNext (downstream (Right value))
--        push (Await upstreamContinuation) downstream
--            = Await (\value => push (upstreamContinuation value) downstream)
--        push (Return value) downstream
--            = pull (Return value) (downstream (Left value))
--
--
--yield : streamOut -> Pipe streamIn streamOut returnIn effects ()
--yield value = Yield (Return ()) value -- We set Return () as the initial continuation, which can then be built upon monadically
--
--
--Effect : (effects: Type -> Type) -> (return: Type) -> Type
--Effect effects return = Pipe Void Void Void effects return
--
--
--partial
--runPipe : Monad effects => Effect effects return -> effects return
--runPipe (Do action) = action >>= \nextPipe => runPipe nextPipe
--runPipe (Yield _ value) = absurd value
--runPipe (Await _ ) = runPipe $ Await (either absurd absurd)
--runPipe (Return value) = pure value 
--
--
--partial
--mapEach : Monad effects => (streamIn -> streamOut) -> Pipe streamIn streamOut return effects return
--mapEach function = Await $ \next => case next of
--    Right value => do
--        yield (function value)
--        mapEach function
--    Left value => Return value
--
--
--foldPipe :
--    (reducer: streamIn -> returnOut -> returnOut)
--    -> (initialValue: returnOut)
--    -> Pipe streamIn Void () effects returnOut
--foldPipe reducer accumulator = Await $ \next => case next of
--    Right value => foldPipe reducer (reducer value accumulator)
--    _ => Return accumulator
--
--
--partial
--readLines : Has [FileIO, Console] effects => Pipe Void String Void (App effects) ()
--readLines = do
--    lift $ putStrLn "Reading next line..."
--    -- TODO: Does this skip the last line?
--    line <- lift getLine
--    eof <- lift $ fEOF stdin
--    if eof
--        then Return ()
--        else do
--            yield line
--            readLines
--
--
--partial
--printEach :
--    (Show streamValue, Has [Console] effects)
--    => Pipe streamValue streamValue () (App effects) ()
--printEach = Await $ \next => case next of
--    Right value => do
--        lift $ putStrLn "Printing..."
--        lift $ putStrLn (show value)
--        yield value
--        printEach
--    _ => Return ()
--
--
--partial
--splitByEmptyLine :
--    Monad effects
--    => Pipe String Void () effects splitReturnOut
--    -> Pipe String splitReturnOut () effects ()
--splitByEmptyLine initialInnerPipeline = runInnerPipe False initialInnerPipeline where
--    runInnerPipe :
--        (hasEnded: Bool)
--        -> Pipe String Void () effects splitReturnOut
--        -> Pipe String splitReturnOut () effects ()
--    runInnerPipe hasEnded (Do action) = do
--        nextPipe <- lift action
--        runInnerPipe hasEnded nextPipe
--    runInnerPipe _ (Yield _ value) = absurd value
--    runInnerPipe _ (Await continuation) =
--        Await $ \next => case next of
--            Right "" => runInnerPipe False (continuation (Left ()))
--            Right nonEmpty => runInnerPipe False (continuation (Right nonEmpty))
--            _ => runInnerPipe True (continuation (Left ()))
--    runInnerPipe hasEnded (Return value) = do
--        yield value
--        if hasEnded
--            then Return ()
--            else runInnerPipe False initialInnerPipeline
--
--
--partial
--parseNat : Monad effects => Pipe String Nat return effects return
--parseNat = mapEach stringToNatOrZ
--
--
--sum : Pipe Nat Void () effects Nat
--sum = foldPipe (+) 0
--
--
--max : Pipe Nat Void () effects Nat
--max = foldPipe maximum 0
--
--
--printReturnValue :
--    (Show return, Has [Console] effects) => Pipe Void Void return (App effects) ()
--printReturnValue = Await $ \next => case next of
--    Right _ => printReturnValue
--    Left value => lift $ putStrLn (show value)
--
--
--partial
--app : Has [FileIO, Console] effects => App effects ()
--app = runPipe $
--    readLines
--    .| splitByEmptyLine (parseNat .| printEach .| sum)
--    .| printEach
--    .| max
--    .| printReturnValue
--
--
--partial
--main : IO ()
--main = run $ handle app
--    (\() => putStr "Ok")
--    (\error : IOError => putStr "Error")