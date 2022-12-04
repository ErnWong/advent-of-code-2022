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


partial
(>>=) :
    Monad effects
    => Pipe streamIn streamOut returnIn {history} effects returnMid
    -> (returnMid -> {0 newHistory: List streamIn} -> Pipe streamIn streamOut returnIn {history = newHistory} effects returnOut)
    -> Pipe streamIn streamOut returnIn {history} effects returnOut
effects >>= function = recurseToReturn effects (\mapHistory, value => function value)


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
    => Pipe streamIn streamMid returnIn {history = historyIn} effects returnMid
    -> Pipe streamMid streamOut returnMid {history = historyMid} effects returnOut
    -> Pipe streamIn streamOut returnIn {history = historyIn} effects returnOut
(.|) = pull where
    mutual
        pull : 
            Monad effects'
            => {0 pullHistoryIn: List streamIn}
            -> {0 pullHistoryMid: List streamMid}
            -> Pipe streamIn streamMid returnIn {history = pullHistoryIn} effects' returnMid
            -> Pipe streamMid streamOut returnMid {history = pullHistoryMid} effects' returnOut
            -> Pipe streamIn streamOut returnIn {history = pullHistoryIn} effects' returnOut
        pull upstream (Do action)
            = Do (action >>= \nextDownstreamPipe => lazyPure (pull upstream nextDownstreamPipe))
        pull upstream (Yield downstreamNext value)
            = Yield (pull upstream downstreamNext) value
        pull upstream (Await downstreamOnReturn downstreamOnStream)
            = push upstream downstreamOnReturn downstreamOnStream
        pull upstream (Return value)
            = Return value

        push :
            Monad effects'
            => {0 historyIn: List streamIn}
            -> {0 historyMid: List streamMid}
            -> Pipe streamIn streamMid returnIn {history = historyIn} effects' returnMid
            -> (returnMid -> Inf (Pipe streamMid streamOut returnMid {history = historyMid} effects' returnOut))
            -> ((value: streamMid) -> Inf (Pipe streamMid streamOut returnMid {history = value :: historyMid} effects' returnOut))
            -> Pipe streamIn streamOut returnIn {history = historyIn} effects' returnOut
        push (Do action) downstreamOnReturn downstreamOnStream
            = Do (action >>= \nextUpstreamPipe => lazyPure (push nextUpstreamPipe downstreamOnReturn downstreamOnStream))
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
    runInnerPipe hasEnded (Do action) = Do (action >>= \nextInnerPipe => lazyPure (runInnerPipe hasEnded nextInnerPipe))
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