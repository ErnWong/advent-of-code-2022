module Main

import Control.App
import Control.App.Console
import Control.App.FileIO
import Control.Monad.Identity
import Control.Monad.Trans
import Data.DPair
import Data.List
import Data.List.Reverse
import Data.Nat
import Data.String
import System.File.Virtual


-- Halting problem go brrr...
%default total


reverseCanJumpAcrossTheEqualsSign :
    (xs, ys : List a)
    -> reverse xs = ys
    -> xs = reverse ys
reverseCanJumpAcrossTheEqualsSign xs ys reverseOnTheLeft =
    let
        reverseItself : (reverse (reverse xs) = reverse (reverse xs))
        reverseItself = Refl

        applyReverseToBothSides : reverse (reverse xs) = reverse ys
        applyReverseToBothSides = rewrite sym reverseOnTheLeft in reverseItself

        twoReversesOnTheLeftCancelsOut : xs = reverse ys
        twoReversesOnTheLeftCancelsOut = rewrite sym $ reverseInvolutive xs in applyReverseToBothSides
    in
        twoReversesOnTheLeftCancelsOut


data IsInputExhausted : Type where
    No : IsInputExhausted
    Yes : (0 upstreamReturnProperty: Type) -> (0 upstreamReturnProof: upstreamReturnProperty) -> IsInputExhausted


noIsNeverYes : (No = Yes _ _) -> Void
noIsNeverYes Refl impossible


NoStreamInvariant : List streamIn -> List streamOut -> Type
NoStreamInvariant _ _ = ()


NoReturnInvariant : IsInputExhausted -> List streamIn -> List streamOut -> returnOut -> Type
NoReturnInvariant _ _ _ _ = ()


ExhaustsInputAnd :
    (List streamIn -> List streamOut -> returnOut -> Type)
    -> IsInputExhausted
    -> List streamIn
    -> List streamOut
    -> returnOut
    -> Type
ExhaustsInputAnd otherReturnInvariant No _ _ _ = Void
ExhaustsInputAnd otherReturnInvariant (Yes _ _) historyIn historyOut returnValue = otherReturnInvariant historyIn historyOut returnValue


||| Pipe implementation ported from Idris v1 to Idris v2 based on QuentinDuval/IdrisPipes
||| Extensions to IdrisPipes: We now index by history (erased at runtime) and an invariant
||| so we can reason about some properties of what a pipe outputs.
|||
||| Note: At the moment, the streamInvariant only holds every time this pipe yields a stream
||| output value, and it's not enforced when awaited a new stream input value. This is because
||| our streamInvariant could be imposing some constraints on what input stream values are allowed
||| but in reality an downstream pipe has no control over what an upstream pipe sends downstream.
||| It might be possible to fix this by making sure the (.|) operator enforces the downstream's
||| stream invariant by restricting what upstream pipes are allowed.
data Pipe :
    (streamIn, streamOut, returnIn: Type)
    -> {0 isInputExhausted : IsInputExhausted} -- TODO: We can pack these into a new PipeState record type
    -> {0 historyIn : List streamIn}
    -> {0 historyOut : List streamOut}
    -> (effects : Type -> Type)
    -> (returnOut : Type)
    -> {default NoStreamInvariant 0 streamInvariant : List streamIn -> List streamOut -> Type}
    -> {default NoReturnInvariant 0 returnInvariant : IsInputExhausted -> List streamIn -> List streamOut -> returnOut -> Type}
    -> Type where

    Do :
        effects (Inf (Pipe
            streamIn -- TODO: We can make these cleaner by using the named function application syntax
            streamOut
            returnIn
            {
                isInputExhausted,
                historyIn,
                historyOut,
                streamInvariant,
                returnInvariant
            }
            effects
            returnOut
        ))
        -> Pipe
            streamIn
            streamOut
            returnIn
            {
                isInputExhausted,
                historyIn,
                historyOut,
                streamInvariant,
                returnInvariant
            }
            effects
            returnOut

    Yield :
        (value: streamOut)
        -> {auto 0 streamInvariantProof : streamInvariant historyIn (value :: historyOut)}
        -> Inf (Pipe
            streamIn
            streamOut
            returnIn
            {
                isInputExhausted,
                historyIn,
                historyOut = (value :: historyOut),
                streamInvariant,
                returnInvariant
            }
            effects
            returnOut
        )
        -> Pipe
            streamIn
            streamOut
            returnIn
            {
                isInputExhausted,
                historyIn,
                historyOut,
                streamInvariant,
                returnInvariant
            }
            effects
            returnOut

    Await :
        (returnIn
            -> {0 upstreamReturnProperty: Type}
            -> (0 upstreamReturnProof: upstreamReturnProperty)
            -> Inf (Pipe
                streamIn
                streamOut
                returnIn
                {
                    isInputExhausted = Yes upstreamReturnProperty upstreamReturnProof,
                    historyIn,
                    historyOut,
                    streamInvariant,
                    returnInvariant
                }
                effects
                returnOut
            ))
        -> ((value: streamIn)
            -> Inf (Pipe
                streamIn
                streamOut
                returnIn
                {
                    isInputExhausted = No,
                    historyIn = (value :: historyIn),
                    historyOut,
                    streamInvariant,
                    returnInvariant
                }
                effects 
                returnOut
            ))
        -> Pipe
            streamIn
            streamOut
            returnIn
            {
                isInputExhausted = No, -- You can't pull from an exhausted upstream.
                historyIn,
                historyOut,
                streamInvariant,
                returnInvariant
            }
            effects
            returnOut

    Return :
        (returnValue: returnOut)
        -> (0 returnInvariantProof : returnInvariant isInputExhausted historyIn historyOut returnValue)
        -> Pipe
            streamIn
            streamOut
            returnIn
            {
                isInputExhausted,
                historyIn,
                historyOut,
                streamInvariant,
                returnInvariant
            }
            effects
            returnOut


||| Idris's type inference has a very hard time figuring this one out, so we explicitly type it
||| instead of using `pure` directly.
lazyPure :
    Monad effects
    => Inf (Pipe
        streamIn
        streamOut
        returnIn
        {
            isInputExhausted,
            historyIn,
            historyOut,
            streamInvariant,
            returnInvariant
        }
        effects
        returnOut
    )
    -> effects (Inf (Pipe
        streamIn
        streamOut
        returnIn
        {
            isInputExhausted,
            historyIn,
            historyOut,
            streamInvariant,
            returnInvariant
        }
        effects
        returnOut
    ))

lazyPure = pure


covering
recurseToReturn :
    Monad effects
    => Pipe
        streamIn
        streamOut
        returnIn
        {
            isInputExhausted = Yes () (),
            historyIn = initialHistoryIn,
            historyOut = initialHistoryOut,
            streamInvariant,
            returnInvariant = NoReturnInvariant
        }
        effects
        returnOutA
    -> (
        (0 mapHistoryIn: List streamIn)
        -> (0 mapHistoryOut: List streamOut)
        -> returnOutA
        -> Pipe
            streamIn
            streamOut
            returnIn
            {
                isInputExhausted,
                historyIn = mapHistoryIn,
                historyOut = mapHistoryOut,
                streamInvariant,
                returnInvariant = NoReturnInvariant
            }
            effects
            returnOutB
        )
    -> Pipe
        streamIn
        streamOut
        returnIn
            {
                isInputExhausted,
                historyIn = initialHistoryIn,
                historyOut = initialHistoryOut,
                streamInvariant,
                returnInvariant = NoReturnInvariant
            }
        effects
        returnOutB

recurseToReturn pipe mapReturn = recurse
        {
            historyIn = initialHistoryIn,
            historyOut = initialHistoryOut
        }
        pipe where

    recurse :
        Pipe
            streamIn
            streamOut
            returnIn
            {
                isInputExhausted = Yes () (),
                historyIn,
                historyOut,
                streamInvariant,
                returnInvariant = NoReturnInvariant
            }
            effects
            returnOutA
        -> Pipe
            streamIn
            streamOut
            returnIn
            {
                isInputExhausted,
                historyIn,
                historyOut,
                streamInvariant,
                returnInvariant = NoReturnInvariant
            }
            effects
            returnOutB

    recurse {historyIn, historyOut} (Do {historyIn, historyOut} action) = Do
        {historyIn, historyOut}
        (do
            next <- action
            lazyPure {streamIn, historyIn, historyOut} (recurse {historyIn, historyOut} next)
        )

    recurse {historyIn, historyOut} (Yield {historyOut, streamInvariantProof} value next)
        = Yield
            value
            (recurse {historyIn, historyOut = (value :: historyOut)} next)

    recurse {historyIn, historyOut} (Return value returnInvariantProof)
        = mapReturn historyIn historyOut value


covering
(>>=) :
    Monad effects
    => Pipe
        streamIn
        streamOut
        returnIn
        {
            isInputExhausted = Yes () (),
            historyIn,
            historyOut,
            streamInvariant,
            returnInvariant = NoReturnInvariant
        }
        effects
        returnMid
    -> (returnMid
        -> {0 newHistoryIn: List streamIn}
        -> {0 newHistoryOut: List streamOut}
        -> Pipe
            streamIn
            streamOut
            returnIn
            {
                isInputExhausted,
                historyIn = newHistoryIn,
                historyOut = newHistoryOut,
                streamInvariant,
                returnInvariant = NoReturnInvariant
            }
            effects
            returnOut
        )
    -> Pipe
        streamIn
        streamOut
        returnIn
        {
            isInputExhausted,
            historyIn,
            historyOut,
            streamInvariant,
            returnInvariant = NoReturnInvariant
        }
        effects
        returnOut
effects >>= function
    = recurseToReturn effects (\mapHistoryIn, mapHistoryOut, value => function value)


lift :
    Monad effects
    => effects returnOut
    -> Pipe streamIn streamOut returnIn {historyIn, returnInvariant = NoReturnInvariant} effects returnOut
lift effects = Do (effects >>= \value => lazyPure (Return value ()))


-- Recurse to Do and map it from Identity to effect
covering
fromPurePipe :
    Monad effects
    => Pipe
        streamIn
        streamOut
        returnIn
        {
            isInputExhausted = overallIsInputExhausted,
            historyIn = overallHistoryIn,
            historyOut = overallHistoryOut,
            returnInvariant = overallReturnInvariant
        }
        Identity
        returnOut
    -> Pipe
        streamIn
        streamOut
        returnIn
        {
            isInputExhausted = overallIsInputExhausted,
            historyIn = overallHistoryIn,
            historyOut = overallHistoryOut,
            returnInvariant = overallReturnInvariant
        } effects returnOut
fromPurePipe pipe = recurse pipe where
    recurse :
        Inf (Pipe
            streamIn
            streamOut
            returnIn
            {
                isInputExhausted = innerIsInputExhausted,
                historyIn = innerHistoryIn,
                historyOut = innerHistoryOut,
                returnInvariant = innerReturnInvariant
            }
            Identity
            returnOut
        )
        -> Pipe
            streamIn
            streamOut
            returnIn
            {
                isInputExhausted = innerIsInputExhausted,
                historyIn = innerHistoryIn,
                historyOut = innerHistoryOut,
                returnInvariant = innerReturnInvariant
            }
            effects
            returnOut
    recurse (Do action) = Do (pure (runIdentity action) >>= \next => lazyPure $ recurse next)
    recurse (Yield {streamInvariantProof} value next) = Yield {streamInvariantProof} value (recurse next)
    recurse (Await onReturn onStream) = Await
        (\value, upstreamReturnProof => recurse $ onReturn value upstreamReturnProof)
        (\value => recurse $ onStream value)
    recurse (Return value returnInvariantProof) = Return value returnInvariantProof


covering
fromInputExhaustedPipe :
    Monad effects
    => Pipe
        streamIn
        streamOut
        returnIn
        {
            isInputExhausted = Yes upstreamReturnProperty upstreamReturnProof,
            streamInvariant = NoStreamInvariant,
            returnInvariant
        }
        effects
        returnOut
    -> Pipe
        streamIn
        streamOut
        returnIn
        {
            isInputExhausted = No,
            streamInvariant = NoStreamInvariant,
            returnInvariant = NoReturnInvariant -- original return invariant is not compatible, so we discard it
        }
        effects
        returnOut
fromInputExhaustedPipe pipe = recurse pipe where
    recurse :
        Pipe
            streamIn
            streamOut
            returnIn
            {
                isInputExhausted = Yes upstreamReturnProperty upstreamReturnProof,
                streamInvariant = NoStreamInvariant,
                returnInvariant
            }
            effects
            returnOut
        -> Pipe
            streamIn
            streamOut
            returnIn
            {
                isInputExhausted = No,
                streamInvariant = NoStreamInvariant,
                returnInvariant = NoReturnInvariant
            }
            effects
            returnOut
    recurse (Do action) = Do (action >>= \next => lazyPure $ recurse next)
    recurse (Yield value next) = Yield value (recurse next)
    recurse (Return value returnInvariantProof) = Return value ()


record ErasedDPair {0 a: Type} {0 b: a -> Type} where
    constructor MkErasedDPair
    0 fst : a
    0 snd : b fst


IsInputExhaustedContainsUpstreamReturnProof :
    (IsInputExhausted -> List streamIn -> List streamOut -> returnOut -> Type)
    -> (historyIn: List streamIn)
    -> (historyOut: List streamOut)
    -> IsInputExhausted
    -> IsInputExhausted
    -> Type
IsInputExhaustedContainsUpstreamReturnProof returnInvariant historyIn historyOut isUpstreamInputExhausted No = ()
IsInputExhaustedContainsUpstreamReturnProof returnInvariant historyIn historyOut isUpstreamInputExhausted (Yes property _)
    = ErasedDPair
        {a = returnOut}
        {b = \finalReturnOut
            => property = returnInvariant isUpstreamInputExhausted historyIn historyOut finalReturnOut
        }


data ErasedThing : (0 a: Type) -> Type where
    MkErasedThing : (0 thing: a) -> ErasedThing a


upstreamReturnProofFromInputExhausted :
    {0 returnInvariant: IsInputExhausted -> List streamIn -> List streamMid -> returnMid -> Type}
    -> {0 historyIn: List streamIn}
    -> {0 historyMid: List streamMid}
    -> {0 isInputExhaustedIn: IsInputExhausted}
    -> (isInputExhaustedMid: IsInputExhausted)
    -> (containsUpstreamReturnProof: IsInputExhaustedContainsUpstreamReturnProof returnInvariant historyIn historyMid isInputExhaustedIn isInputExhaustedMid)
    -> (proofThatWeDidExhaust: Exists $ \property => Exists $ \returnProof => (isInputExhaustedMid = Yes property returnProof))
    -> ErasedThing $ ErasedDPair
        {
            a = returnMid,
            b = \finalReturnMid => returnInvariant isInputExhaustedIn historyIn historyMid finalReturnMid
        }
upstreamReturnProofFromInputExhausted isInputExhaustedMid@No _ proofThatWeDidExhaust = void $ noIsNeverYes $
    (the (No = isInputExhaustedMid) Refl)
    `trans`
    (the (isInputExhaustedMid = Yes _ _) (snd $ snd proofThatWeDidExhaust))
upstreamReturnProofFromInputExhausted (Yes property returnProof) containsUpstreamReturnProof _ = MkErasedThing $ MkErasedDPair
    (fst containsUpstreamReturnProof)
    (
        rewrite
            the (returnInvariant isInputExhaustedIn historyIn historyMid (fst containsUpstreamReturnProof) = property)
                $ sym $ snd containsUpstreamReturnProof
        in
            returnProof
    )


composeStreamInvariants :
    (List streamIn -> List streamMid -> Type)
    -> (List streamMid -> List streamOut -> Type)
    -> List streamIn
    -> List streamOut
    -> Type
composeStreamInvariants streamInvariantUpstream streamInvariantDownstream currentHistoryIn currentHistoryOut
    = Exists $ \currentHistoryMid => (
        streamInvariantUpstream currentHistoryIn currentHistoryMid,
        streamInvariantDownstream currentHistoryMid currentHistoryOut
    )


%prefix_record_projections off
record ComposedReturnProof
    {0 streamIn: Type}
    {0 streamMid: Type}
    {0 returnMid: Type}
    (returnInvariantUpstream: IsInputExhausted -> List streamIn -> List streamMid -> returnMid -> Type)
    (returnInvariantDownstream: IsInputExhausted -> List streamMid -> List streamOut -> returnOut -> Type)
    (isInputExhaustedIn : IsInputExhausted)
    (historyIn : List streamIn)
    (historyOut : List streamOut)
    (returnOutValue : returnOut)
    where
        constructor MkComposedReturnProof
        0 isInputExhaustedMid: IsInputExhausted
        0 historyMid: List streamMid
        0 downstreamProof: returnInvariantDownstream isInputExhaustedMid historyMid historyOut returnOutValue
        0 midExhaustedContainsUpstreamReturnProof: IsInputExhaustedContainsUpstreamReturnProof returnInvariantUpstream historyIn historyMid isInputEhaustedIn isInputExhaustedMid


infixr 9 .|
||| Operator to compose two pipes together, where the streamOut and returnOut of the upstream pipe flow
||| into the streamIn and returnIn of the downstream pipe, similar to that of Unix streams and pipes.
covering --todo totality
(.|) :
    Monad effects
    => Pipe
        streamIn
        streamMid
        returnIn
        {
            isInputExhausted = isInputExhaustedIn,
            historyIn,
            historyOut = historyMid,
            streamInvariant = streamInvariantUpstream,
            returnInvariant = returnInvariantUpstream
        }
        effects
        returnMid
    -> Pipe
        streamMid
        streamOut
        returnMid
        {
            isInputExhausted = No,
            historyIn = historyMid,
            historyOut,
            streamInvariant = streamInvariantDownstream,
            returnInvariant = returnInvariantDownstream
        }
        effects
        returnOut
    -> Pipe
        streamIn
        streamOut
        returnIn
        {
            isInputExhausted = isInputExhaustedIn,
            historyIn,
            historyOut,
            -- It's too hard and messy for now to compose two stream invariants together,
            -- since it's not something that's always satisfied (i.e. we don't enforce it when
            -- a pipe awaits a new value, so the stream invariant could be broken at that point).
            streamInvariant = NoStreamInvariant,
            returnInvariant = ComposedReturnProof returnInvariantUpstream returnInvariantDownstream
        }
        effects
        returnOut
(.|) = pull {midExhaustedContainsUpstreamReturnProof = ()} where
    mutual
        pull : 
            Monad effects'
            => {0 pullIsInputExhaustedIn: IsInputExhausted}
            -> {0 pullIsInputExhaustedMid: IsInputExhausted}
            -> {0 pullHistoryIn: List streamIn}
            -> {0 pullHistoryMid: List streamMid}
            -> {0 midExhaustedContainsUpstreamReturnProof:
                IsInputExhaustedContainsUpstreamReturnProof
                    returnInvariantUpstream
                    pullHistoryIn
                    pullHistoryMid
                    pullIsInputExhaustedIn
                    pullIsInputExhaustedMid
            }
            -> Pipe
                streamIn
                streamMid
                returnIn
                {
                    isInputExhausted = pullIsInputExhaustedIn,
                    historyIn = pullHistoryIn,
                    historyOut = pullHistoryMid,
                    streamInvariant = streamInvariantUpstream,
                    returnInvariant = returnInvariantUpstream
                }
                effects'
                returnMid
            -> Pipe
                streamMid
                streamOut
                returnMid
                {
                    isInputExhausted = pullIsInputExhaustedMid,
                    historyIn = pullHistoryMid,
                    historyOut = pullHistoryOut,
                    streamInvariant = streamInvariantDownstream,
                    returnInvariant = returnInvariantDownstream
                }
                effects'
                returnOut
            -> Pipe
                streamIn
                streamOut
                returnIn
                {
                    isInputExhausted = pullIsInputExhaustedIn,
                    historyIn = pullHistoryIn,
                    historyOut = pullHistoryOut,
                    streamInvariant = NoStreamInvariant,
                    returnInvariant = ComposedReturnProof returnInvariantUpstream returnInvariantDownstream
                }
                effects'
                returnOut
        pull upstream (Do action)
            = Do (action >>= \nextDownstreamPipe => lazyPure (pull
                {midExhaustedContainsUpstreamReturnProof}
                upstream
                nextDownstreamPipe
            ))
        pull upstream (Yield {streamInvariantProof = newStreamInvariantProofDownstream} value downstreamNext)
            = Yield
                value
                (
                    pull {midExhaustedContainsUpstreamReturnProof}
                        upstream
                        downstreamNext
                )
        pull upstream (Await downstreamOnReturn downstreamOnStream)
            = push upstream downstreamOnReturn downstreamOnStream
        pull {pullHistoryMid} upstream (Return value returnInvariantProof)
            = Return value $ MkComposedReturnProof {
                isInputExhaustedMid = pullIsInputExhaustedMid,
                historyMid = pullHistoryMid,
                downstreamProof = returnInvariantProof,
                midExhaustedContainsUpstreamReturnProof
            }

        push :
            Monad effects'
            => {0 pushIsInputExhaustedIn: IsInputExhausted}
            -> {0 pushHistoryIn: List streamIn}
            -> {0 pushHistoryMid: List streamMid}
            -> Pipe
                streamIn
                streamMid
                returnIn
                {
                    isInputExhausted = pushIsInputExhaustedIn,
                    historyIn = pushHistoryIn,
                    historyOut = pushHistoryMid,
                    streamInvariant = streamInvariantUpstream,
                    returnInvariant = returnInvariantUpstream
                }
                effects'
                returnMid
            -> (returnMid
                -> {0 upstreamReturnProperty: Type}
                -> (0 upstreamReturnProof: upstreamReturnProperty)
                -> Inf (Pipe
                    streamMid
                    streamOut
                    returnMid
                    {
                        isInputExhausted = Yes upstreamReturnProperty upstreamReturnProof,
                        historyIn = pushHistoryMid,
                        historyOut = pushHistoryOut,
                        streamInvariant = streamInvariantDownstream,
                        returnInvariant = returnInvariantDownstream
                    }
                    effects'
                    returnOut
                ))
            -> ((value: streamMid)
                -> Inf (Pipe
                    streamMid
                    streamOut
                    returnMid
                    {
                        isInputExhausted = No,
                        historyIn = value :: pushHistoryMid,
                        historyOut = pushHistoryOut,
                        streamInvariant = streamInvariantDownstream,
                        returnInvariant = returnInvariantDownstream
                    }
                    effects'
                    returnOut))
            -> Pipe
                streamIn
                streamOut
                returnIn
                {
                    isInputExhausted = pushIsInputExhaustedIn,
                    historyIn = pushHistoryIn,
                    historyOut = pushHistoryOut,
                    streamInvariant = NoStreamInvariant,
                    returnInvariant = ComposedReturnProof returnInvariantUpstream returnInvariantDownstream
                }
                effects'
                returnOut
        push (Do action) downstreamOnReturn downstreamOnStream
            = Do (action >>= \nextUpstreamPipe => lazyPure (push nextUpstreamPipe downstreamOnReturn downstreamOnStream))
        push (Yield value upstreamNext) downstreamOnReturn downstreamOnStream
            = pull
                {midExhaustedContainsUpstreamReturnProof = ()}
                upstreamNext
                (downstreamOnStream value)
        push (Await upstreamOnReturn upstreamOnStream) downstreamOnReturn downstreamOnStream
            = Await
                (\value, upstreamReturnProof => push (upstreamOnReturn value upstreamReturnProof) downstreamOnReturn downstreamOnStream)
                (\value => push (upstreamOnStream value) downstreamOnReturn downstreamOnStream)
        push (Return value returnInvariantProof) downstreamOnReturn downstreamOnStream
            = pull
                {
                    pullIsInputExhaustedIn = pushIsInputExhaustedIn,
                    pullIsInputExhaustedMid = Yes _ returnInvariantProof,
                    midExhaustedContainsUpstreamReturnProof = MkErasedDPair value Refl
                }
                (Return value returnInvariantProof)
                (downstreamOnReturn value returnInvariantProof)


yield :
    (value: streamOut)
    -> {auto 0 streamInvariantProof : streamInvariant historyIn (value :: historyOut)}
    -> Pipe
        streamIn
        streamOut
        returnIn
        {
            isInputExhausted,
            historyIn,
            historyOut,
            streamInvariant
        }
        effects
        ()
yield {streamInvariantProof} value = Yield value {streamInvariantProof} (Return () ()) -- We set Return () as the initial continuation, which can then be built upon monadically


Effect :
    (effects: Type -> Type) -> (return: Type)
    -> {default NoReturnInvariant 0 returnInvariant: IsInputExhausted -> List Void -> List Void -> return -> Type} -> Type
Effect effects return = Pipe
    Void
    Void
    Void
    {
        isInputExhausted = Yes () (),
        historyIn = [],
        historyOut = [],
        returnInvariant
    }
    effects
    return


covering
runPipeWithInvariant :
    Monad effects
    => Effect effects return {returnInvariant}
    -> effects (Subset return (\returnValue => returnInvariant (Yes () ()) [] [] returnValue))
runPipeWithInvariant (Do action) = action >>= \nextPipe => runPipeWithInvariant nextPipe
runPipeWithInvariant (Yield value _) = absurd value
runPipeWithInvariant (Return value {returnInvariantProof}) = pure (Element value returnInvariantProof)


covering
runPipe :
    Monad effects
    => Effect effects return {returnInvariant}
    -> effects return
runPipe pipe = map fst $ runPipeWithInvariant pipe


fromListReturnInvariant : List streamOut -> IsInputExhausted -> List Void -> List streamOut -> () -> Type
fromListReturnInvariant list _ _ finalHistoryOut _ = reverse finalHistoryOut = list


fromListReturnInvariantOnlyDependsOnHistoryOut :
    (list: List streamOut)
    -> (historyOut: List streamOut)
    -> {0 isInputEhaustedIn: IsInputExhausted}
    -> {0 historyIn: List Void}
    -> (fromListReturnInvariant list isInputExhaustedIn historyIn historyOut ()
        = (reverse historyOut = list))
fromListReturnInvariantOnlyDependsOnHistoryOut list historyOut = Refl


covering
fromList :
    Monad effects
    => (list: List streamOut)
    -> Pipe
        Void
        streamOut
        Void
        {
            isInputExhausted = Yes () (),
            historyIn = [],
            historyOut = [],
            streamInvariant = \currentHistoryIn, currentHistoryOut
                => (suffix: List streamOut ** (reverse currentHistoryOut) ++ suffix = list),
            returnInvariant = fromListReturnInvariant list
        }
        effects
        ()
fromList list = recurse list proofBaseCase where
    proofBaseCase : list = list
    proofBaseCase = Refl

    recurse :
        (remaining: List streamOut)
        -> (0 inductionHypothesis: (reverse historyOut) ++ remaining = list)
        -> Pipe Void streamOut Void
            {historyOut,
            streamInvariant = \currentHistoryIn, currentHistoryOut
                => (suffix: List streamOut ** (reverse currentHistoryOut) ++ suffix = list),
            returnInvariant = \finalIsInputExhausted, finalHistoryIn, finalHistoryOut, finalReturnOut
                => reverse finalHistoryOut = list
            } effects ()

    recurse [] historyIsPrefix = Return () {returnInvariantProof = hypothesisRearranged} where
        0 inductionHypothesis : (reverse historyOut) ++ [] = list
        inductionHypothesis = historyIsPrefix

        0 hypothesisRearranged : reverse historyOut = list
        hypothesisRearranged = rewrite reverseOntoSpec [] historyOut in inductionHypothesis

    recurse (x :: xs) historyIsPrefix =
        Yield x
            {streamInvariantProof = (xs ** inductionStep)}
            (recurse xs inductionStep) where
                reverseMovesHeadToEnd : (x: a) -> (xs : List a) -> reverse (x :: xs) = (reverse xs) ++ [x]
                reverseMovesHeadToEnd x xs = reverseOntoSpec [x] xs

                0 inductionHypothesis : (reverse historyOut) ++ (x :: xs) = list
                inductionHypothesis = historyIsPrefix

                0 hypothesisRearranged : ((reverse historyOut) ++ [x]) ++ xs = list
                hypothesisRearranged = rewrite sym (appendAssociative (reverse historyOut) [x] xs) in inductionHypothesis

                0 inductionStep : (reverse (x :: historyOut)) ++ xs = list
                inductionStep = rewrite reverseMovesHeadToEnd x historyOut in hypothesisRearranged


covering
runPurePipeWithList :
    Pipe
        streamIn
        Void
        ()
        {
            isInputExhausted = No,
            historyIn = [],
            historyOut = [],
            returnInvariant
        }
        Identity
        returnOut
    -> (input: List streamIn)
    -> Subset returnOut $
        \returnValue
            => ComposedReturnProof
                {
                    streamIn = Void,
                    returnMid = ()
                }
                (fromListReturnInvariant input)
                returnInvariant
                (Yes () ())
                []
                []
                returnValue
runPurePipeWithList pipe list = runIdentity $ runPipeWithInvariant $ fromList list .| pipe


covering
runInputExhaustingPurePipeWithList :
    Pipe
        streamIn
        Void
        ()
        {
            isInputExhausted = No,
            historyIn = [],
            historyOut = [],
            returnInvariant = ExhaustsInputAnd returnInvariant
        }
        Identity
        returnOut
    -> (input: List streamIn)
    -> Subset returnOut $ \returnValue => returnInvariant (reverse input) [] returnValue
runInputExhaustingPurePipeWithList pipe list =
    let
        originalResult = runPurePipeWithList pipe list

        Element returnValue proofs = originalResult

        inputNotExhaustedIsContradiction :
            (proofs.isInputExhaustedMid = No)
            -> (Void = ExhaustsInputAnd returnInvariant proofs.isInputExhaustedMid proofs.historyMid [] returnValue)
        inputNotExhaustedIsContradiction ifInputIsntExhausted = rewrite ifInputIsntExhausted in Refl

        inputExhaustedGivesDownstreamReturnInvariant :
            (proofs.isInputExhaustedMid = Yes _ _)
            -> (returnInvariant proofs.historyMid [] returnValue = ExhaustsInputAnd returnInvariant proofs.isInputExhaustedMid proofs.historyMid [] returnValue)
        inputExhaustedGivesDownstreamReturnInvariant ifInputExhausted = rewrite ifInputExhausted in Refl

        extractIsInputExhaustedEquality :
            (isInputExhausted: IsInputExhausted)
            -> Either
                (isInputExhausted = No)
                (Exists {type = Type} $ \a =>
                    Exists {type = a} $ \b =>
                        isInputExhausted = Yes a b)
        extractIsInputExhaustedEquality No = Left Refl
        extractIsInputExhaustedEquality (Yes a b) = Right (Evidence a $ Evidence b Refl)

        0 midIsExhausted : 
            (Exists {type = Type} $ \a =>
                Exists {type = a} $ \b =>
                    proofs.isInputExhaustedMid = Yes a b)
        midIsExhausted = case (extractIsInputExhaustedEquality proofs.isInputExhaustedMid) of
            Left proofThatItsNotExhausted => void $
                rewrite
                    inputNotExhaustedIsContradiction proofThatItsNotExhausted
                in
                    proofs.downstreamProof
            Right proofThatItsExhausted => proofThatItsExhausted

        0 downstreamReturnInvariantProof : returnInvariant proofs.historyMid [] returnValue
        downstreamReturnInvariantProof =
            rewrite
                inputExhaustedGivesDownstreamReturnInvariant (snd $ snd midIsExhausted)
            in
                proofs.downstreamProof

        0 proofThatReverseOfHistoryMidEqualsList : reverse proofs.historyMid = list
        proofThatReverseOfHistoryMidEqualsList =
            let
                MkErasedThing returnProofPair = upstreamReturnProofFromInputExhausted
                    proofs.isInputExhaustedMid
                    proofs.midExhaustedContainsUpstreamReturnProof
                    midIsExhausted
            in
                snd $ returnProofPair

        0 proofThatHistoryMidEqualsReverseOfList : proofs.historyMid = reverse list
        proofThatHistoryMidEqualsReverseOfList
            = reverseCanJumpAcrossTheEqualsSign proofs.historyMid list proofThatReverseOfHistoryMidEqualsList

        0 finalProof : returnInvariant (reverse list) [] returnValue
        finalProof = rewrite sym proofThatHistoryMidEqualsReverseOfList in downstreamReturnInvariantProof
    in
        Element returnValue finalProof


covering
mapEach :
    Monad effects
    => (streamIn -> streamOut)
    -> Pipe
        streamIn
        streamOut
        return
        {
            isInputExhausted = No
        }
        effects
        return
mapEach function = Await  
    (\returnValue, returnProof => Return returnValue ())
    (\streamValue => do
        _ <- yield (function streamValue)
        mapEach function
    )


covering --todo
foldPipe :
    (reducer: streamIn -> returnOut -> returnOut)
    -> (initialValue: returnOut)
    -> Pipe
        streamIn
        Void
        () 
        {
            isInputExhausted = No,
            historyIn = [],
            historyOut = [],
            returnInvariant = ExhaustsInputAnd $ \finalHistoryIn, finalHistoryOut, finalReturn
                => finalReturn = foldr reducer initialValue finalHistoryIn
        }
        Identity
        returnOut

foldPipe reducer initialValue = recurse [] initialValue proofBaseCase where
    proofBaseCase : initialValue = foldr reducer initialValue []
    proofBaseCase = Refl

    recurse :
        (0 historyIn: List streamIn)
        -> (accumulator: returnOut)
        -> (0 inductionHypothesis: accumulator = foldr reducer initialValue historyIn)
        -> Pipe
            streamIn
            Void
            ()
            {
                isInputExhausted = No,
                historyIn,
                historyOut = [],
                returnInvariant = ExhaustsInputAnd $ \finalHistoryIn, finalHistoryOut, finalReturn
                    => finalReturn = foldr reducer initialValue finalHistoryIn
            }
            Identity
            returnOut

    recurse historyIn accumulator proofThatAccumulatorEqualsFoldr =
        Await
            (\returnValue, returnProof => Return accumulator proofThatAccumulatorEqualsFoldr)
            onStream
        where
            onStream :
                (value: streamIn)
                -> Inf (Pipe
                    streamIn
                    Void
                    ()
                    {
                        isInputExhausted = No,
                        historyIn = (value :: historyIn),
                        historyOut = [],
                        returnInvariant = ExhaustsInputAnd $ \finalHistoryIn, finalHistoryOut, finalReturn
                            => finalReturn = foldr reducer initialValue finalHistoryIn
                    }
                    Identity
                    returnOut
                )
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
            then Return () ()
            else do
                _ <- yield line
                recurse


covering
printEach :
    (Show streamValue, Has [Console] effects)
    => Pipe streamValue streamValue () {isInputExhausted = No, historyIn = []} (App effects) ()
printEach = recurse where
    recurse : Pipe streamValue streamValue () {isInputExhausted = No} (App effects) ()
    recurse = Await
        (\returnValue, returnProof => Return () ())
        (\streamValue => do
            _ <- lift $ putStrLn "Printing..."
            _ <- lift $ putStrLn (show streamValue)
            _ <- yield streamValue
            recurse
        )


covering
splitByEmptyLine :
    Monad effects
    => Pipe
        String
        Void
        ()
        {
            isInputExhausted = No,
            historyIn = [],
            returnInvariant
        }
        effects
        splitReturnOut
    -> Pipe
        String
        splitReturnOut
        ()
        {
            isInputExhausted = No,
            historyIn = [],
            returnInvariant = NoReturnInvariant
        }
        effects
        ()
splitByEmptyLine initialInnerPipeline = runInnerPipe No initialInnerPipeline where
    runInnerPipe :
        (isInputExhausted: IsInputExhausted)
        -> Pipe
            String
            Void
            ()
            {
                isInputExhausted,
                historyIn = innerHistoryIn,
                historyOut = innerHistoryOut,
                returnInvariant = innerReturnInvariant -- Allow the inner return invariant to change as we could be dropping it
            }
            effects
            splitReturnOut
        -> Pipe
            String
            splitReturnOut
            ()
            {
                isInputExhausted,
                historyIn = outerHistoryIn,
                historyOut = outerHistoryOut,
                returnInvariant = NoReturnInvariant
            }
            effects
            ()
    runInnerPipe hasEnded (Do action) = Do (action >>= \nextInnerPipe
        => lazyPure (runInnerPipe hasEnded nextInnerPipe))
    runInnerPipe _ (Yield value _) = absurd value
    runInnerPipe {innerHistoryIn, innerHistoryOut} No (Await onReturn onStream) =
        Await
            (\returnValue, returnProof => runInnerPipe (Yes _ _) (onReturn () returnProof)
                )
            (\streamValue => case streamValue of
                "" => runInnerPipe {innerHistoryIn, innerHistoryOut} No (fromInputExhaustedPipe $ onReturn () ())
                nonEmpty => runInnerPipe No (onStream nonEmpty))
    runInnerPipe isInputExhausted (Return value returnInvariantProof) = do
        _ <- yield value
        case isInputExhausted of
            Yes _ _ => Return () ()
            No => runInnerPipe No initialInnerPipeline


covering
parseNat : Monad effects => Pipe String Nat return {isInputExhausted = No, historyIn = []} effects return
parseNat = mapEach stringToNatOrZ


covering
sum :
    Monad effects
    => Pipe
        Nat
        Void
        ()
        {
            isInputExhausted = No,
            historyIn = [],
            historyOut = [],
            returnInvariant = ExhaustsInputAnd $ \finalHistoryIn, finalHistoryOut, finalReturn
                => finalReturn = foldr (+) 0 finalHistoryIn
        }
        effects
        Nat
sum = fromPurePipe $ foldPipe (+) 0


maxReturnInvariant : List Nat -> List Void -> Nat -> Type
maxReturnInvariant finalHistoryIn finalHistoryOut finalReturn = (finalReturn = foldr Data.Nat.maximum 0 finalHistoryIn)


covering
max :
    Monad effects
    => Pipe
        Nat
        Void
        ()
        {
            isInputExhausted = No,
            historyIn = [],
            historyOut = [],
            returnInvariant = ExhaustsInputAnd Main.maxReturnInvariant
        }
        effects
        Nat
max = fromPurePipe $ foldPipe maximum 0


forAllPossibleInputs_maxPipeIsEquivalentToFoldrMax :
    (input: List Nat)
    -> ErasedThing (fst (runInputExhaustingPurePipeWithList {returnInvariant = Main.maxReturnInvariant} Main.max input) = foldr Data.Nat.maximum 0 (reverse input))
forAllPossibleInputs_maxPipeIsEquivalentToFoldrMax input = let
        x = MkErasedThing $ snd $ runInputExhaustingPurePipeWithList max input
    in ?todo


printReturnValue :
    (Show return, Has [Console] effects) => Pipe Void Void return {isInputExhausted = No, historyIn = []} (App effects) ()
printReturnValue = recurse where
    recurse : Pipe Void Void return {isInputExhausted = No} (App effects) ()
    recurse = Await
        (\returnValue, returnProof => lift $ putStrLn (show returnValue))
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
