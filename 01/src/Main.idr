module Main

import Control.App
import Control.App.Console
import Control.App.FileIO
import Control.Monad.Identity
import Control.Monad.Trans
import Data.Nat
import Data.String
import System.File.Virtual


-- Halting problem go brrr...
%default total


NoInvariant : List streamIn -> returnOut -> Type
NoInvariant _ _ = ()

-- data PipeInvariant streamIn returnOut
--     = NoInvariant
--     | Invariant (List streamIn -> returnOut -> Type)
-- 
-- 
-- data Funny : Bool -> Type where
--     MkFunny : {default False 0 yes:Bool} -> (if yes then (Nat, Nat) else Nat) -> Funny yes
-- 
-- 
-- ||| If the pipe has an invariant, then make sure that variant is fulfilled when the pipe returns.
-- ||| Otherwise, the pipe is free to return any value of type `returnOut`.
-- pipeReturnType : (returnOut: Type) -> PipeInvariant streamIn returnOut -> Type
-- pipeReturnType returnOut (Invariant invariant) = DPair returnOut (invariant [])
-- pipeReturnType returnOut NoInvariant = returnOut


||| Pipe implementation ported from Idris v1 to Idris v2 based on QuentinDuval/IdrisPipes
||| Extensions to IdrisPipes: We now index by history (erased at runtime) and an invariant
||| so we can reason about some properties of what a pipe outputs.
data Pipe :
    (streamIn, streamOut, returnIn: Type)
    -> {0 history : List streamIn}
    ---> {default NoInvariant 0 invariant : PipeInvariant streamIn returnOut}
    -> (effects : Type -> Type)
    -> (returnOut : Type)
    -> {default NoInvariant 0 invariant : List streamIn -> returnOut -> Type}
    -> Type where
    Do :
        effects (Inf (Pipe streamIn streamOut returnIn {history, invariant} effects returnOut))
        -> Pipe streamIn streamOut returnIn {history, invariant} effects returnOut
    Yield :
        Inf (Pipe streamIn streamOut returnIn {history, invariant} effects returnOut)
        -> streamOut
        -> Pipe streamIn streamOut returnIn {history, invariant} effects returnOut
    Await :
        (returnIn -> Inf (Pipe streamIn streamOut returnIn {history, invariant} effects returnOut))
        -> ((value: streamIn)
            -> Inf (Pipe streamIn streamOut returnIn {history = (value :: history), invariant} effects returnOut))
        -> Pipe streamIn streamOut returnIn {history, invariant} effects returnOut
    Return :
        --pipeReturnType returnOut invariant
        --(case invariant of
        --    NoInvariant => returnOut
        --    Invariant invariant => DPair returnOut (invariant history)--(value: returnOut, invariant history value)
        --)
        (returnValue: returnOut)
        -> {auto 0 invariantProof : invariant history returnValue}
        -> Pipe streamIn streamOut returnIn {history, invariant} effects returnOut


||| Idris's type inference has a very hard time figuring this one out, so we explicitly type it
||| instead of using `pure` directly.
lazyPure :
    Monad effects
    => Inf (Pipe streamIn streamOut returnIn {history, invariant} effects returnOut)
    -> effects (Inf (Pipe streamIn streamOut returnIn {history, invariant} effects returnOut))
lazyPure = pure


partial
recurseToReturn :
    Monad effects
    => Pipe streamIn streamOut returnIn {history = initialHistory, invariant = invariantA} effects returnOutA
    -> ((0 mapHistory: List streamIn)
        -> returnOutA
        -> (0 invariantA: List streamIn -> returnOut -> Type)
        -> Pipe streamIn streamOut returnIn {history = mapHistory, invariant = invariantB} effects returnOutB)
    -> Pipe streamIn streamOut returnIn {history = initialHistory, invariant = invariantB} effects returnOutB
recurseToReturn pipe mapReturn = recurse {history = initialHistory} pipe where
    recurse :
        Pipe streamIn streamOut returnIn {history, invariant = invariantA} effects returnOutA
        -> Pipe streamIn streamOut returnIn {history, invariant = invariantA} effects returnOutB
    recurse {history} (Do {history} action) = Do
        {history}
        (do
            next <- action
            lazyPure {streamIn} {history} (recurse {history} next)
        )
    recurse {history} (Yield next value) = Yield {history} (recurse {history} next) value
    recurse {history} (Await onReturn onStream) = Await
        {history}
        (\end => recurse {history} (onReturn end))
        (\streamNext => recurse {history = (streamNext :: history)} (onStream streamNext))
    recurse {history} (Return value) = mapReturn history value


--Monad effects
--=> Functor (Pipe streamIn streamOut returnIn {history} effects) where
--    map function pipe = assert_total
--        recurseToReturn pipe mapReturnWithFunction where
--            mapReturnWithFunction:
--                (0 mapHistory: List streamIn)
--                -> a
--                -> (0 invariantA: PipeInvariant streamIn a)
--                -> Pipe streamIn streamOut returnIn {history = mapHistory, invariant = invariantB} effects b
--            mapReturnWithFunction mapHistory value invariantA
--                = Return {history = mapHistory, invariant = mapInvariant invariantA} (function value) where
--                    mapInvariant:
--                        PipeInvariant streamIn a
--                        -> PipeInvariant streamIn b
--                    mapInvariant NoInvariant = NoInvariant
--                    mapInvariant (Invariant invariant) = Invariant (\history, returnValueA => )

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
    -> Pipe streamIn streamOut returnIn {history, invariant} effects returnOut
lift effects = Do (effects >>= \value => lazyPure (Return value))


-- Recurse to Do and map it from Identity to effect
partial
fromPurePipe :
    Monad effects
    => Pipe streamIn streamOut returnIn {history = overallHistory, invariant = overallInvariant} Identity returnOut
    -> Pipe streamIn streamOut returnIn {history = overallHistory, invariant = overallInvariant} effects returnOut
fromPurePipe pipe = recurse pipe where
    recurse :
        Inf (Pipe streamIn streamOut returnIn {history = innerHistory, invariant = innerInvariant} Identity returnOut)
        -> Pipe streamIn streamOut returnIn {history = innerHistory, invariant = innerInvariant} effects returnOut
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
            => {0 pushHistoryIn: List streamIn}
            -> {0 pushHistoryMid: List streamMid}
            -> Pipe streamIn streamMid returnIn {history = pushHistoryIn} effects' returnMid
            -> (returnMid
                -> Inf (Pipe streamMid streamOut returnMid {history = pushHistoryMid} effects' returnOut))
            -> ((value: streamMid)
                -> Inf (Pipe streamMid streamOut returnMid {history = value :: pushHistoryMid} effects' returnOut))
            -> Pipe streamIn streamOut returnIn {history = pushHistoryIn} effects' returnOut
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
fromList : Monad effects => List streamOut -> Pipe Void streamOut Void {history = []} effects ()
fromList = recurse where
    recurse : List streamOut -> Pipe Void streamOut Void effects ()
    recurse [] = Return ()
    recurse (x :: xs) = yield x >>= (\() => recurse xs)


partial
runPurePipeWithList :
    Pipe streamIn Void () Identity returnOut
    -> List streamIn
    -> returnOut
runPurePipeWithList pipe list = runIdentity $ runPipe (fromList list .| pipe)


partial
mapEach : Monad effects => (streamIn -> streamOut) -> Pipe streamIn streamOut return effects return
mapEach function = Await  
    (\returnValue => Return returnValue)
    (\streamValue => do
        _ <- yield (function streamValue)
        mapEach function
    )


--partial
--ProofThatFoldPipeIsJustLikeFold : Type
--ProofThatFoldPipeIsJustLikeFold =
--    -- Our pipe...
--    {streamIn: Type}
--    -> {returnOut: Type}
--    -> (pipe: Pipe streamIn Void () {history = []} Identity returnOut)
--    -- ...behaves just like folding over a list using the folllowing reducer...
--    -> (reducer: returnOut -> streamIn -> returnOut)
--    -- ...when starting with an accumulator value of...
--    -> (initialValue: returnOut)
--
--    -- By that, we mean that, GIVEN any possible input list...
--    -> (inputList: List streamIn)
--
--    -- THEN we can show propositional equality between folding on that list
--    -- and the return value of running the pipe...
--    -> (runPurePipeWithList pipe inputList = foldr reducer initialValue inputList)
--
--
--theproof : ProofThatFoldPipeIsJustLikeFold
--theproof pipe reducer initialValue [] = ?todoproofnilRefl
--theproof pipe reducer initialValue [x] = ?todoproofsingleRefl
--theproof pipe reducer initialValue (x :: xs) = theproof pipe reducer (theproof pipe reducer initialValue xs) [x]


--data FoldPipe : (history: List streamIn) -> Pipe streamIn Void () {history} Identity returnOut -> Type where
--    Initial : FoldPipe [] (Await
--        (\_ => Return initialValue)
--        (\streamValue =>)
--    )
--    Await :
--        (returnIn -> Inf (FoldPipe history (Return ())))
--        -> ((value: streamIn)
--            -> Inf (Pipe streamIn streamOut returnIn {history = (value :: history)} effects returnOut))
--        -> FoldPipe (Await onReturn onStream)
--    Return :
--        (value: returnOut) -> FoldPipe history (Return ())


--equalityIsTransitive : a = b -> b = c -> a = c
--equalityIsTransitive Refl Refl = Refl


partial --todo
foldPipe :
    (reducer: streamIn -> returnOut -> returnOut)
    -> (initialValue: returnOut)
    -> (
        pipe:
            Pipe streamIn Void () {history = []} Identity returnOut
        --** ProofThatFoldPipeIsJustLikeFold pipe reducer initialValue
        ** (inputList: List streamIn)
            -> (runPurePipeWithList pipe inputList = foldr reducer initialValue inputList)
        )
foldPipe reducer initialValue = (recurse [] initialValue proofBaseCase ** ?todoOverallProof) where
    proofBaseCase : initialValue = foldr reducer initialValue []
    proofBaseCase = Refl

    recurse :
        (0 history: List streamIn)
        -> (accumulator: returnOut)
        -> (accumulator = foldr reducer initialValue history)
        -> (
            --pipe:
                Pipe streamIn Void () {history} Identity returnOut
            --** ProofThatFoldPipeIsJustLikeFold pipe reducer initialValue
            --** (inputList: List streamIn)
            --    -> (runPurePipeWithList pipe ((reverse history) ++ inputList) = foldr reducer initialValue inputList)
            --** accumulator = foldr reducer initialValue (newestInput :: previousInputs)
            )
    recurse history accumulator proofThatAccumulatorEqualsFoldr =
        Await
            (\_ => Return accumulator)
            onStream
        where
            onStream :
                (value: streamIn)
                -> Inf (Pipe streamIn Void () {history = (value :: history)} Identity returnOut)
            onStream value = recurse (value :: history) (reducer value accumulator) previousAccumulatorAppliedOnceEqualsNextFoldr
                where
                    previousFoldrAppliedOnceEqualsNextFoldr :
                        reducer value (foldr reducer initialValue history)
                        = foldr reducer initialValue (value :: history)
                    previousFoldrAppliedOnceEqualsNextFoldr = Refl

                    previousAccumulatorAppliedOnceEqualsNextFoldr :
                        reducer value accumulator
                        = foldr reducer initialValue (value :: history)
                    previousAccumulatorAppliedOnceEqualsNextFoldr =
                        rewrite proofThatAccumulatorEqualsFoldr
                        in previousFoldrAppliedOnceEqualsNextFoldr


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
    => Pipe String Void () {history = [], invariant = NoInvariant} effects splitReturnOut
    -> Pipe String splitReturnOut () {history = [], invariant = NoInvariant} effects ()
splitByEmptyLine initialInnerPipeline = runInnerPipe False initialInnerPipeline where
    runInnerPipe :
        (hasEnded: Bool)
        -> Pipe String Void () {history = innerHistory, invariant = NoInvariant} effects splitReturnOut
        -> Pipe String splitReturnOut () {history = outerHistory, invariant = NoInvariant} effects ()
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
parseNat : Monad effects => Pipe String Nat return {history = []} effects return
parseNat = mapEach stringToNatOrZ


partial
sum : Monad effects => Pipe Nat Void () {history = []} effects Nat
sum = fromPurePipe $ fst $ foldPipe (+) 0


partial
max : Monad effects => Pipe Nat Void () {history = []} effects Nat
max = fromPurePipe $ fst $ foldPipe maximum 0


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