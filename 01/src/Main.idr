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


NoInvariant : List streamIn -> returnOut -> Type
NoInvariant _ _ = ()


||| Pipe implementation ported from Idris v1 to Idris v2 based on QuentinDuval/IdrisPipes
||| Extensions to IdrisPipes: We now index by history (erased at runtime) and an invariant
||| so we can reason about some properties of what a pipe outputs.
data Pipe :
    (streamIn, streamOut, returnIn: Type)
    -> {0 historyIn : List streamIn}
    -> (effects : Type -> Type)
    -> (returnOut : Type)
    -> {default NoInvariant 0 invariant : List streamIn -> returnOut -> Type}
    -> Type where
    Do :
        effects (Inf (Pipe streamIn streamOut returnIn {historyIn, invariant} effects returnOut))
        -> Pipe streamIn streamOut returnIn {historyIn, invariant} effects returnOut
    Yield :
        Inf (Pipe streamIn streamOut returnIn {historyIn, invariant} effects returnOut)
        -> streamOut
        -> Pipe streamIn streamOut returnIn {historyIn, invariant} effects returnOut
    Await :
        (returnIn -> Inf (Pipe streamIn streamOut returnIn {historyIn, invariant} effects returnOut))
        -> ((value: streamIn)
            -> Inf (Pipe streamIn streamOut returnIn {historyIn = (value :: historyIn), invariant} effects returnOut))
        -> Pipe streamIn streamOut returnIn {historyIn, invariant} effects returnOut
    Return :
        (returnValue: returnOut)
        -> {auto 0 invariantProof : invariant historyIn returnValue}
        -> Pipe streamIn streamOut returnIn {historyIn, invariant} effects returnOut


||| Idris's type inference has a very hard time figuring this one out, so we explicitly type it
||| instead of using `pure` directly.
lazyPure :
    Monad effects
    => Inf (Pipe streamIn streamOut returnIn {historyIn, invariant} effects returnOut)
    -> effects (Inf (Pipe streamIn streamOut returnIn {historyIn, invariant} effects returnOut))
lazyPure = pure


partial
recurseToReturn :
    Monad effects
    => Pipe streamIn streamOut returnIn {historyIn = initialHistoryIn, invariant = NoInvariant} effects returnOutA
    -> ((0 mapHistoryIn: List streamIn)
        -> returnOutA
        -> Pipe streamIn streamOut returnIn {historyIn = mapHistoryIn, invariant = NoInvariant} effects returnOutB)
    -> Pipe streamIn streamOut returnIn {historyIn = initialHistoryIn, invariant = NoInvariant} effects returnOutB
recurseToReturn pipe mapReturn = recurse {historyIn = initialHistoryIn} pipe where
    recurse :
        Pipe streamIn streamOut returnIn {historyIn, invariant = NoInvariant} effects returnOutA
        -> Pipe streamIn streamOut returnIn {historyIn, invariant = NoInvariant} effects returnOutB
    recurse {historyIn} (Do {historyIn} action) = Do
        {historyIn}
        (do
            next <- action
            lazyPure {streamIn} {historyIn} (recurse {historyIn} next)
        )
    recurse {historyIn} (Yield next value) = Yield {historyIn} (recurse {historyIn} next) value
    recurse {historyIn} (Await onReturn onStream) = Await
        {historyIn}
        (\end => recurse {historyIn} (onReturn end))
        (\streamNext => recurse {historyIn = (streamNext :: historyIn)} (onStream streamNext))
    recurse {historyIn} (Return value) = mapReturn historyIn value


partial
(>>=) :
    Monad effects
    => Pipe streamIn streamOut returnIn {historyIn, invariant = NoInvariant} effects returnMid
    -> (returnMid -> {0 newHistoryIn: List streamIn} -> Pipe streamIn streamOut returnIn {historyIn = newHistoryIn, invariant = NoInvariant} effects returnOut)
    -> Pipe streamIn streamOut returnIn {historyIn, invariant = NoInvariant} effects returnOut
effects >>= function = recurseToReturn effects (\mapHistoryIn, value => function value)


lift :
    Monad effects
    => effects returnOut
    -> Pipe streamIn streamOut returnIn {historyIn, invariant = NoInvariant} effects returnOut
lift effects = Do (effects >>= \value => lazyPure (Return value))


-- Recurse to Do and map it from Identity to effect
partial
fromPurePipe :
    Monad effects
    => Pipe streamIn streamOut returnIn {historyIn = overallHistoryIn, invariant = overallInvariant} Identity returnOut
    -> Pipe streamIn streamOut returnIn {historyIn = overallHistoryIn, invariant = overallInvariant} effects returnOut
fromPurePipe pipe = recurse pipe where
    recurse :
        Inf (Pipe streamIn streamOut returnIn {historyIn = innerHistoryIn, invariant = innerInvariant} Identity returnOut)
        -> Pipe streamIn streamOut returnIn {historyIn = innerHistoryIn, invariant = innerInvariant} effects returnOut
    recurse (Do action) = Do (pure (runIdentity action) >>= \next => lazyPure $ recurse next)
    recurse (Yield next value) = Yield (recurse next) value
    recurse (Await onReturn onStream) = Await
        (\value => recurse $ onReturn value)
        (\value => recurse $ onStream value)
    recurse (Return value) = Return value


infixr 9 .|
||| The pipe operator chains two pipes together.
partial --todo totality
(.|) :
    Monad effects
    => Pipe streamIn streamMid returnIn {historyIn, invariant = invariantA} effects returnMid
    -> Pipe streamMid streamOut returnMid {historyIn = historyMid, invariant = invariantB} effects returnOut
    -> Pipe streamIn streamOut returnIn {historyIn, invariant = NoInvariant} effects returnOut
    --newInvariant = \finalHistoryIn, returnValue =>
    --  Exists (List streamMid) \historyMid => 
    --      (invariantB historyMid returnValue, streamInvariantA finalHistoryIn historyMid)
(.|) = pull where
    mutual
        pull : 
            Monad effects'
            => {0 pullHistoryIn: List streamIn}
            -> {0 pullHistoryMid: List streamMid}
            -> Pipe streamIn streamMid returnIn {historyIn = pullHistoryIn, invariant = invariantA} effects' returnMid
            -> Pipe streamMid streamOut returnMid {historyIn = pullHistoryMid, invariant = invariantB} effects' returnOut
            -> Pipe streamIn streamOut returnIn {historyIn = pullHistoryIn, invariant = NoInvariant} effects' returnOut
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
            => {0 pushHistoryIn: List streamIn}
            -> {0 pushHistoryMid: List streamMid}
            -> Pipe streamIn streamMid returnIn {historyIn = pushHistoryIn, invariant = invariantA} effects' returnMid
            -> (returnMid
                -> Inf (Pipe streamMid streamOut returnMid {historyIn = pushHistoryMid, invariant = invariantB} effects' returnOut))
            -> ((value: streamMid)
                -> Inf (Pipe streamMid streamOut returnMid {historyIn = value :: pushHistoryMid, invariant = invariantB} effects' returnOut))
            -> Pipe streamIn streamOut returnIn {historyIn = pushHistoryIn, invariant = NoInvariant} effects' returnOut
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


Effect :
    (effects: Type -> Type) -> (return: Type)
    -> {default NoInvariant 0 invariant: List Void -> return -> Type} -> Type
Effect effects return = Pipe Void Void Void {historyIn = [], invariant} effects return


partial
runPipeWithInvariant :
    Monad effects
    => Effect effects return {invariant}
    -> effects (Subset return (\returnValue => invariant [] returnValue))
runPipeWithInvariant (Do action) = action >>= \nextPipe => runPipeWithInvariant nextPipe
runPipeWithInvariant (Yield _ value) = absurd value
runPipeWithInvariant (Await _ _) = runPipeWithInvariant $ Await {invariant} absurd (\x => absurd x)
runPipeWithInvariant (Return value {invariantProof}) = pure (Element value invariantProof)
--runPipeWithInvariant (Return value {invariantProof}) = thePure (value ** invariantProof) where
    --thePure : (value: return ** invariant [] value) -> effects (value: return ** invariant [] value)
    --thePure = pure


partial
runPipe :
    Monad effects
    => Effect effects return {invariant}
    -> effects return
runPipe pipe = map fst $ runPipeWithInvariant pipe


partial
fromList : Monad effects => List streamOut -> Pipe Void streamOut Void {historyIn = []} effects ()
fromList = recurse where
    recurse : List streamOut -> Pipe Void streamOut Void effects ()
    recurse [] = Return ()
    recurse (x :: xs) = yield x >>= (\() => recurse xs)


--pipeWithListInput :
--    Monad effects
--    => (input: List streamIn)
--    -> Pipe streamIn Void () {historyIn = [], invariant = innerInvariant} effects returnOut
--    -> Effect effects returnOut {invariant = \finalHistoryIn, returnValue => innerInvariant input returnValue}
--pipeWithListInput input pipe = todoInvariantPreservingPipeComposition (fromList input) pipe where
--    todoInvariantPreservingPipeComposition :
--        Monad effects
--        => Pipe Void streamIn Void {historyIn = [], invariant = NoInvariant} effects ()
--        -> Pipe streamIn Void () {historyIn = [], invariant = innerInvariant} effects returnOut
--        -> Effect effects returnOut {invariant = \finalHistoryIn, returnValue => innerInvariant input returnValue}
--    todoInvariantPreservingPipeComposition = ?todoComposeRhs


partial
runPurePipeWithList :
    Pipe streamIn Void () {historyIn = [], invariant} Identity returnOut
    -> (input: List streamIn)
    -> Subset returnOut (\returnValue => invariant input returnValue)
runPurePipeWithList pipe list = ?todoRunPurePipeWithList --runIdentity $ runPipeWithInvariant (todoPipeCompose (fromList list) pipe) where


partial
mapEach : Monad effects => (streamIn -> streamOut) -> Pipe streamIn streamOut return effects return
mapEach function = Await  
    (\returnValue => Return returnValue)
    (\streamValue => do
        _ <- yield (function streamValue)
        mapEach function
    )


partial --todo
foldPipe :
    (reducer: streamIn -> returnOut -> returnOut)
    -> (initialValue: returnOut)
    -> Pipe streamIn Void () {historyIn = [], invariant = \finalHistoryIn, finalReturn => finalReturn = foldr reducer initialValue finalHistoryIn} Identity returnOut
foldPipe reducer initialValue = recurse [] initialValue proofBaseCase where
    proofBaseCase : initialValue = foldr reducer initialValue []
    proofBaseCase = Refl

    recurse :
        (0 historyIn: List streamIn)
        -> (accumulator: returnOut)
        -> (accumulator = foldr reducer initialValue historyIn)
        -> Pipe streamIn Void () {historyIn, invariant = \finalHistoryIn, finalReturn => finalReturn = foldr reducer initialValue finalHistoryIn} Identity returnOut
    recurse historyIn accumulator proofThatAccumulatorEqualsFoldr =
        Await
            (\_ => Return accumulator)
            onStream
        where
            onStream :
                (value: streamIn)
                -> Inf (Pipe streamIn Void () {historyIn = (value :: historyIn), invariant = \finalHistoryIn, finalReturn => finalReturn = foldr reducer initialValue finalHistoryIn} Identity returnOut)
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


partial
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


partial
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


partial
splitByEmptyLine :
    Monad effects
    => Pipe String Void () {historyIn = [], invariant = NoInvariant} effects splitReturnOut
    -> Pipe String splitReturnOut () {historyIn = [], invariant = NoInvariant} effects ()
splitByEmptyLine initialInnerPipeline = runInnerPipe False initialInnerPipeline where
    runInnerPipe :
        (hasEnded: Bool)
        -> Pipe String Void () {historyIn = innerHistoryIn, invariant = NoInvariant} effects splitReturnOut
        -> Pipe String splitReturnOut () {historyIn = outerHistoryIn, invariant = NoInvariant} effects ()
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
            then Return () {invariantProof = ()}
            else runInnerPipe False initialInnerPipeline


partial
parseNat : Monad effects => Pipe String Nat return {historyIn = []} effects return
parseNat = mapEach stringToNatOrZ


partial
sum : Monad effects => Pipe Nat Void () {historyIn = [],
            invariant = \finalHistoryIn, finalReturn => finalReturn = foldr (+) 0 finalHistoryIn}
        effects Nat
sum = fromPurePipe $ foldPipe (+) 0


partial
max : Monad effects => Pipe Nat Void () {historyIn = [],
        invariant = \finalHistoryIn, finalReturn => finalReturn = foldr Data.Nat.maximum 0 finalHistoryIn}
    effects Nat
max = fromPurePipe $ foldPipe maximum 0


printReturnValue :
    (Show return, Has [Console] effects) => Pipe Void Void return {historyIn = []} (App effects) ()
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