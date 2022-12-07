module Main

import Control.App
import Control.App.Console
import Control.App.FileIO
import Control.Monad.Identity
import Control.Monad.Trans
import Data.DPair
import Data.Nat
import Data.String
import System.File.Virtual


-- Halting problem go brrr...
%default total


NoInvariant : List streamIn -> out -> Type
NoInvariant _ _ = ()


||| Pipe implementation ported from Idris v1 to Idris v2 based on QuentinDuval/IdrisPipes
||| Extensions to IdrisPipes: We now index by history (erased at runtime) and an invariant
||| so we can reason about some properties of what a pipe outputs.
data Pipe :
    (streamIn, streamOut, returnIn: Type)
    -> {0 historyIn : List streamIn}
    -> {0 historyOut : List streamOut}
    -> (effects : Type -> Type)
    -> (returnOut : Type)
    -> {default NoInvariant 0 streamInvariant : List streamIn -> List streamOut -> Type}
    -> {default NoInvariant 0 returnInvariant : List streamIn -> returnOut -> Type}
    -> Type where
    Do :
        effects (Inf (Pipe streamIn streamOut returnIn {historyIn, historyOut, streamInvariant, returnInvariant} effects returnOut))
        -> Pipe streamIn streamOut returnIn {historyIn, historyOut, streamInvariant, returnInvariant} effects returnOut
    Yield :
        (value: streamOut)
        -> {auto 0 streamInvariantProof : streamInvariant historyIn (value :: historyOut)}
        -> Inf (Pipe streamIn streamOut returnIn {historyIn, historyOut = (value :: historyOut), streamInvariant, returnInvariant} effects returnOut)
        -> Pipe streamIn streamOut returnIn {historyIn, historyOut, streamInvariant, returnInvariant} effects returnOut
    Await :
        (returnIn -> Inf (Pipe streamIn streamOut returnIn {historyIn, historyOut, streamInvariant, returnInvariant} effects returnOut))
        -> ((value: streamIn)
            -> Inf (Pipe streamIn streamOut returnIn {historyIn = (value :: historyIn), historyOut, streamInvariant, returnInvariant} effects returnOut))
        -> Pipe streamIn streamOut returnIn {historyIn, historyOut, streamInvariant, returnInvariant} effects returnOut
    Return :
        (returnValue: returnOut)
        -> {auto 0 returnInvariantProof : returnInvariant historyIn returnValue}
        -> Pipe streamIn streamOut returnIn {historyIn, historyOut, streamInvariant, returnInvariant} effects returnOut


||| Idris's type inference has a very hard time figuring this one out, so we explicitly type it
||| instead of using `pure` directly.
lazyPure :
    Monad effects
    => Inf (Pipe streamIn streamOut returnIn {historyIn, historyOut, returnInvariant} effects returnOut)
    -> effects (Inf (Pipe streamIn streamOut returnIn {historyIn, historyOut, returnInvariant} effects returnOut))
lazyPure = pure


covering
recurseToReturn :
    Monad effects
    => Pipe streamIn streamOut returnIn {historyIn = initialHistoryIn, historyOut = initialHistoryOut, returnInvariant = NoInvariant} effects returnOutA
    -> ((0 mapHistoryIn: List streamIn)
        -> (0 mapHistoryOut: List streamOut)
        -> returnOutA
        -> Pipe streamIn streamOut returnIn {historyIn = mapHistoryIn, historyOut = mapHistoryOut, returnInvariant = NoInvariant} effects returnOutB)
    -> Pipe streamIn streamOut returnIn {historyIn = initialHistoryIn, historyOut = initialHistoryOut, returnInvariant = NoInvariant} effects returnOutB
recurseToReturn pipe mapReturn = recurse {historyIn = initialHistoryIn, historyOut = initialHistoryOut} pipe where
    recurse :
        Pipe streamIn streamOut returnIn {historyIn, historyOut, returnInvariant = NoInvariant} effects returnOutA
        -> Pipe streamIn streamOut returnIn {historyIn, historyOut, returnInvariant = NoInvariant} effects returnOutB
    recurse {historyIn, historyOut} (Do {historyIn, historyOut} action) = Do
        {historyIn, historyOut}
        (do
            next <- action
            lazyPure {streamIn, historyIn, historyOut} (recurse {historyIn, historyOut} next)
        )
    recurse {historyIn, historyOut} (Yield {historyOut} value next) = Yield {historyIn, historyOut} value (recurse {historyIn, historyOut = (value :: historyOut)} next)
    recurse {historyIn, historyOut} (Await onReturn onStream) = Await
        {historyIn, historyOut}
        (\end => recurse {historyIn, historyOut} (onReturn end))
        (\streamNext => recurse {historyIn = (streamNext :: historyIn), historyOut} (onStream streamNext))
    recurse {historyIn, historyOut} (Return value) = mapReturn historyIn historyOut value


covering
(>>=) :
    Monad effects
    => Pipe streamIn streamOut returnIn {historyIn, historyOut, returnInvariant = NoInvariant} effects returnMid
    -> (returnMid -> {0 newHistoryIn: List streamIn} -> {0 newHistoryOut: List streamOut} -> Pipe streamIn streamOut returnIn {historyIn = newHistoryIn, historyOut = newHistoryOut, returnInvariant = NoInvariant} effects returnOut)
    -> Pipe streamIn streamOut returnIn {historyIn, historyOut, returnInvariant = NoInvariant} effects returnOut
effects >>= function = recurseToReturn effects (\mapHistoryIn, mapHistoryOut, value => function value)


lift :
    Monad effects
    => effects returnOut
    -> Pipe streamIn streamOut returnIn {historyIn, returnInvariant = NoInvariant} effects returnOut
lift effects = Do (effects >>= \value => lazyPure (Return value))


-- Recurse to Do and map it from Identity to effect
covering
fromPurePipe :
    Monad effects
    => Pipe streamIn streamOut returnIn {historyIn = overallHistoryIn, historyOut = overallHistoryOut, returnInvariant = overallReturnInvariant} Identity returnOut
    -> Pipe streamIn streamOut returnIn {historyIn = overallHistoryIn, historyOut = overallHistoryOut, returnInvariant = overallReturnInvariant} effects returnOut
fromPurePipe pipe = recurse pipe where
    recurse :
        Inf (Pipe streamIn streamOut returnIn {historyIn = innerHistoryIn, returnInvariant = innerReturnInvariant} Identity returnOut)
        -> Pipe streamIn streamOut returnIn {historyIn = innerHistoryIn, returnInvariant = innerReturnInvariant} effects returnOut
    recurse (Do action) = Do (pure (runIdentity action) >>= \next => lazyPure $ recurse next)
    recurse (Yield value next) = Yield value (recurse next)
    recurse (Await onReturn onStream) = Await
        (\value => recurse $ onReturn value)
        (\value => recurse $ onStream value)
    recurse (Return value) = Return value


infixr 9 .|
||| The pipe operator chains two pipes together.
covering --todo totality
(.|) :
    Monad effects
    => Pipe streamIn streamMid returnIn {historyIn, historyOut = historyMid, returnInvariant = returnInvariantA} effects returnMid
    -> Pipe streamMid streamOut returnMid {historyIn = historyMid, historyOut, returnInvariant = returnInvariantB} effects returnOut
    -> Pipe streamIn streamOut returnIn {historyIn, historyOut, returnInvariant = NoInvariant} effects returnOut
    --newInvariant = \finalHistoryIn, returnValue =>
    --  Exists (List streamMid) \historyMid => 
    --      (returnInvariantB historyMid returnValue, streamInvariantA finalHistoryIn historyMid)
(.|) = pull where
    mutual
        pull : 
            Monad effects'
            => {0 pullHistoryIn: List streamIn}
            -> {0 pullHistoryMid: List streamMid}
            -> Pipe streamIn streamMid returnIn {historyIn = pullHistoryIn, historyOut = pullHistoryMid, returnInvariant = returnInvariantA} effects' returnMid
            -> Pipe streamMid streamOut returnMid {historyIn = pullHistoryMid, historyOut = pullHistoryOut, returnInvariant = returnInvariantB} effects' returnOut
            -> Pipe streamIn streamOut returnIn {historyIn = pullHistoryIn, historyOut = pullHistoryOut, returnInvariant = NoInvariant} effects' returnOut
        pull upstream (Do action)
            = Do (action >>= \nextDownstreamPipe => lazyPure (pull upstream nextDownstreamPipe))
        pull upstream (Yield value downstreamNext)
            = Yield value (pull upstream downstreamNext)
        pull upstream (Await downstreamOnReturn downstreamOnStream)
            = push upstream downstreamOnReturn downstreamOnStream
        pull upstream (Return value)
            = Return value

        push :
            Monad effects'
            => {0 pushHistoryIn: List streamIn}
            -> {0 pushHistoryMid: List streamMid}
            -> Pipe streamIn streamMid returnIn {historyIn = pushHistoryIn, historyOut = pushHistoryMid, returnInvariant = returnInvariantA} effects' returnMid
            -> (returnMid
                -> Inf (Pipe streamMid streamOut returnMid {historyIn = pushHistoryMid, historyOut = pushHistoryOut, returnInvariant = returnInvariantB} effects' returnOut))
            -> ((value: streamMid)
                -> Inf (Pipe streamMid streamOut returnMid {historyIn = value :: pushHistoryMid, historyOut = pushHistoryOut, returnInvariant = returnInvariantB} effects' returnOut))
            -> Pipe streamIn streamOut returnIn {historyIn = pushHistoryIn, historyOut = pushHistoryOut, returnInvariant = NoInvariant} effects' returnOut
        push (Do action) downstreamOnReturn downstreamOnStream
            = Do (action >>= \nextUpstreamPipe => lazyPure (push nextUpstreamPipe downstreamOnReturn downstreamOnStream))
        push (Yield value upstreamNext) downstreamOnReturn downstreamOnStream
            = pull upstreamNext (downstreamOnStream value)
        push (Await upstreamOnReturn upstreamOnStream) downstreamOnReturn downstreamOnStream
            = Await
                (\value => push (upstreamOnReturn value) downstreamOnReturn downstreamOnStream)
                (\value => push (upstreamOnStream value) downstreamOnReturn downstreamOnStream)
        push (Return value) downstreamOnReturn downstreamOnStream
            = pull (Return value) (downstreamOnReturn value)


yield : streamOut -> Pipe streamIn streamOut returnIn effects ()
yield value = Yield value (Return ()) -- We set Return () as the initial continuation, which can then be built upon monadically


Effect :
    (effects: Type -> Type) -> (return: Type)
    -> {default NoInvariant 0 returnInvariant: List Void -> return -> Type} -> Type
Effect effects return = Pipe Void Void Void {historyIn = [], historyOut = [], returnInvariant} effects return


covering
runPipeWithInvariant :
    Monad effects
    => Effect effects return {returnInvariant}
    -> effects (Subset return (\returnValue => returnInvariant [] returnValue))
runPipeWithInvariant (Do action) = action >>= \nextPipe => runPipeWithInvariant nextPipe
runPipeWithInvariant (Yield value _) = absurd value
runPipeWithInvariant (Await _ _) = runPipeWithInvariant $ Await {returnInvariant} absurd (\x => absurd x)
runPipeWithInvariant (Return value {returnInvariantProof}) = pure (Element value returnInvariantProof)
--runPipeWithInvariant (Return value {returnInvariantProof}) = thePure (value ** returnInvariantProof) where
    --thePure : (value: return ** returnInvariant [] value) -> effects (value: return ** returnInvariant [] value)
    --thePure = pure


covering
runPipe :
    Monad effects
    => Effect effects return {returnInvariant}
    -> effects return
runPipe pipe = map fst $ runPipeWithInvariant pipe


covering
fromList : Monad effects => List streamOut -> Pipe Void streamOut Void {historyIn = []} effects ()
fromList = recurse where
    recurse : List streamOut -> Pipe Void streamOut Void effects ()
    recurse [] = Return ()
    recurse (x :: xs) = yield x >>= (\() => recurse xs)


--pipeWithListInput :
--    Monad effects
--    => (input: List streamIn)
--    -> Pipe streamIn Void () {historyIn = [], returnInvariant = innerReturnInvariant} effects returnOut
--    -> Effect effects returnOut {returnInvariant = \finalHistoryIn, returnValue => innerReturnInvariant input returnValue}
--pipeWithListInput input pipe = todoInvariantPreservingPipeComposition (fromList input) pipe where
--    todoInvariantPreservingPipeComposition :
--        Monad effects
--        => Pipe Void streamIn Void {historyIn = [], returnInvariant = NoInvariant} effects ()
--        -> Pipe streamIn Void () {historyIn = [], returnInvariant = innerReturnInvariant} effects returnOut
--        -> Effect effects returnOut {returnInvariant = \finalHistoryIn, returnValue => innerReturnInvariant input returnValue}
--    todoInvariantPreservingPipeComposition = ?todoComposeRhs


covering
runPurePipeWithList :
    Pipe streamIn Void () {historyIn = [], returnInvariant} Identity returnOut
    -> (input: List streamIn)
    -> Subset returnOut (\returnValue => returnInvariant input returnValue)
runPurePipeWithList pipe list = ?todoRunPurePipeWithList --runIdentity $ runPipeWithInvariant (todoPipeCompose (fromList list) pipe) where


covering
mapEach : Monad effects => (streamIn -> streamOut) -> Pipe streamIn streamOut return effects return
mapEach function = Await  
    (\returnValue => Return returnValue)
    (\streamValue => do
        _ <- yield (function streamValue)
        mapEach function
    )


covering --todo
foldPipe :
    (reducer: streamIn -> returnOut -> returnOut)
    -> (initialValue: returnOut)
    -> Pipe streamIn Void () {historyIn = [], returnInvariant = \finalHistoryIn, finalReturn => finalReturn = foldr reducer initialValue finalHistoryIn} Identity returnOut
foldPipe reducer initialValue = recurse [] initialValue proofBaseCase where
    proofBaseCase : initialValue = foldr reducer initialValue []
    proofBaseCase = Refl

    recurse :
        (0 historyIn: List streamIn)
        -> (accumulator: returnOut)
        -> (accumulator = foldr reducer initialValue historyIn)
        -> Pipe streamIn Void () {historyIn, returnInvariant = \finalHistoryIn, finalReturn => finalReturn = foldr reducer initialValue finalHistoryIn} Identity returnOut
    recurse historyIn accumulator proofThatAccumulatorEqualsFoldr =
        Await
            (\_ => Return accumulator)
            onStream
        where
            onStream :
                (value: streamIn)
                -> Inf (Pipe streamIn Void () {historyIn = (value :: historyIn), returnInvariant = \finalHistoryIn, finalReturn => finalReturn = foldr reducer initialValue finalHistoryIn} Identity returnOut)
            onStream value = recurse (value :: historyIn) (reducer value accumulator) previousAccumulatorAppliedOnceEqualsNextFoldr
                where
                    previousFoldrAppliedOnceEqualsNextFoldr :
                        reducer value (foldr reducer initialValue historyIn)
                        = foldr reducer initialValue (value :: historyIn)
                    previousFoldrAppliedOnceEqualsNextFoldr = Refl

                    previousAccumulatorAppliedOnceEqualsNextFoldr :
                        reducer value accumulator
                        = foldr reducer initialValue (value :: historyIn)
                    previousAccumulatorAppliedOnceEqualsNextFoldr =
                        rewrite proofThatAccumulatorEqualsFoldr
                        in previousFoldrAppliedOnceEqualsNextFoldr


covering
readLines : Has [FileIO, Console] effects => Pipe Void String Void {historyIn = []} (App effects) ()
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


covering
printEach :
    (Show streamValue, Has [Console] effects)
    => Pipe streamValue streamValue () {historyIn = []} (App effects) ()
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


covering
splitByEmptyLine :
    Monad effects
    => Pipe String Void () {historyIn = [], returnInvariant = NoInvariant} effects splitReturnOut
    -> Pipe String splitReturnOut () {historyIn = [], returnInvariant = NoInvariant} effects ()
splitByEmptyLine initialInnerPipeline = runInnerPipe False initialInnerPipeline where
    runInnerPipe :
        (hasEnded: Bool)
        -> Pipe String Void () {historyIn = innerHistoryIn, returnInvariant = NoInvariant} effects splitReturnOut
        -> Pipe String splitReturnOut () {historyIn = outerHistoryIn, returnInvariant = NoInvariant} effects ()
    runInnerPipe hasEnded (Do action) = Do (action >>= \nextInnerPipe => lazyPure (runInnerPipe hasEnded nextInnerPipe))
    runInnerPipe _ (Yield value _) = absurd value
    runInnerPipe _ (Await onReturn onStream) =
        Await
            (\_ => runInnerPipe True (onReturn ()))
            (\streamValue => case streamValue of
                "" => runInnerPipe False (onReturn ())
                nonEmpty => runInnerPipe False (onStream nonEmpty))
    runInnerPipe hasEnded (Return value) = do
        _ <- yield value
        if hasEnded
            then Return () {returnInvariantProof = ()}
            else runInnerPipe False initialInnerPipeline


covering
parseNat : Monad effects => Pipe String Nat return {historyIn = []} effects return
parseNat = mapEach stringToNatOrZ


covering
sum : Monad effects => Pipe Nat Void () {historyIn = [], historyOut = [],
            returnInvariant = \finalHistoryIn, finalReturn => finalReturn = foldr (+) 0 finalHistoryIn}
        effects Nat
sum = fromPurePipe $ foldPipe (+) 0


covering
max : Monad effects => Pipe Nat Void () {historyIn = [], historyOut = [],
        returnInvariant = \finalHistoryIn, finalReturn => finalReturn = foldr Data.Nat.maximum 0 finalHistoryIn}
    effects Nat
max = fromPurePipe $ foldPipe maximum 0


printReturnValue :
    (Show return, Has [Console] effects) => Pipe Void Void return {historyIn = []} (App effects) ()
printReturnValue = recurse where
    recurse : Pipe Void Void return (App effects) ()
    recurse = Await
        (\returnValue => lift $ putStrLn (show returnValue))
        (\_ => recurse)


covering
app : Has [FileIO, Console] effects => App effects ()
app = runPipe $
    readLines
    .| splitByEmptyLine (parseNat .| printEach .| sum)
    .| printEach
    .| max
    .| printReturnValue


covering
main : IO ()
main = run $ handle app
    (\() => putStr "Ok")
    (\error : IOError => putStr "Error")