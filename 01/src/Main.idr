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


data IsInputExhausted : Type where
    No : IsInputExhausted
    Yes : (0 upstreamReturnProperty: Type) -> (0 upstreamReturnProof: upstreamReturnProperty) -> IsInputExhausted


NoStreamInvariant : List streamIn -> List streamOut -> Type
NoStreamInvariant _ _ = ()


NoReturnInvariant : IsInputExhausted -> List streamIn -> List streamOut -> returnOut -> Type
NoReturnInvariant _ _ _ _ = ()


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
    --> {auto 0 streamInvariantProof : streamInvariant historyIn historyOut} We can't do this because a pipe doesn't have control over what it receives
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
                --streamInvariantProof
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
                --streamInvariantProof
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
                --streamInvariantProof
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
                --streamInvariantProof = oldStreamInvariantProof
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
                    --streamInvariantProof
                }
                effects
                returnOut
            ))
        -> ((value: streamIn)
            ---> (0 newStreamInvariantProof : streamInvariant (value :: historyIn) historyOut) Here is the problem - why should it satisfy an arbitrary invariant?
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
                    --streamInvariantProof = newStreamInvariantProof
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
                --streamInvariantProof
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
                --streamInvariantProof
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
            --streamInvariantProof
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
            --streamInvariantProof
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
            --streamInvariantProof = initialStreamInvariantProof
        }
        effects
        returnOutA
    -> (--(0 mapIsInputExhausted: IsInputExhausted)
        (0 mapHistoryIn: List streamIn)
        -> (0 mapHistoryOut: List streamOut)
        ---> (0 mapStreamInvariantProof: streamInvariant mapHistoryIn mapHistoryOut)
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
                --streamInvariantProof = mapStreamInvariantProof
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
                --streamInvariantProof = initialStreamInvariantProof
            }
        effects
        returnOutB

recurseToReturn pipe mapReturn = recurse
        {
            --isInputExhausted = initialIsInputExhausted,
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
                --streamInvariantProof
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
                --streamInvariantProof
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
            --{historyIn, historyOut, streamInvariantProof}
            value
            --(recurse {historyIn, historyOut = (value :: historyOut), streamInvariantProof} next)
            (recurse {historyIn, historyOut = (value :: historyOut)} next)

    --recurse {historyIn, historyOut} (Await onReturn onStream) = Await
    --    {historyIn, historyOut}
    --    (\end => recurse {historyIn, historyOut} (onReturn end))
    --    (\streamNext => recurse {historyIn = (streamNext :: historyIn), historyOut} (onStream streamNext))

    --recurse {isInputExhausted, historyIn, historyOut} (Return value) = mapReturn isInputExhausted historyIn historyOut value
    --recurse {historyIn, historyOut, streamInvariantProof} (Return value returnInvariantProof)
    --    = mapReturn historyIn historyOut streamInvariantProof value
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
            --streamInvariantProof
        }
        effects
        returnMid
    -> (returnMid
        ---> {0 newIsInputExhausted: IsInputExhausted}
        -> {0 newHistoryIn: List streamIn}
        -> {0 newHistoryOut: List streamOut}
        ---> {0 newStreamInvariantProof: streamInvariant newHistoryIn newHistoryOut}
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
                --streamInvariantProof = newStreamInvariantProof
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
            --streamInvariantProof
        }
        effects
        returnOut
effects >>= function
    --= recurseToReturn effects (\mapHistoryIn, mapHistoryOut, mapStreamInvariantProof, value => function value)
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
            --streamInvariantProof = overallStreamInvariantProof
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
            --streamInvariantProof = overallStreamInvariantProof
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
                --streamInvariantProof = innerStreamInvariantProof
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
                --streamInvariantProof = innerStreamInvariantProof
            }
            effects
            returnOut
    recurse (Do action) = Do (pure (runIdentity action) >>= \next => lazyPure $ recurse next)
    recurse (Yield {streamInvariantProof} value next) = Yield {streamInvariantProof} value (recurse next)
    recurse (Await onReturn onStream) = Await
        (\value, upstreamReturnProof => recurse $ onReturn value upstreamReturnProof)
        --(\value, newStreamInvariantProof => recurse $ onStream value newStreamInvariantProof)
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
            --streamInvariantProof = ()
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
            --streamInvariantProof = ()
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
                --streamInvariantProof --= ()
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
                --streamInvariantProof --=()
            }
            effects
            returnOut
    recurse (Do action) = Do (action >>= \next => lazyPure $ recurse next)
    --recurse (Yield {streamInvariantProof = newStreamInvariantProof} value next) = Yield {streamInvariantProof} value (recurse {streamInvariantProof = newStreamInvariantProof} next)
    --recurse (Yield {streamInvariantProof = newStreamInvariantProof} value next) = ?todofrominputexhausted--Yield {oldStreamInvariantProof = streamInvariantProof} value (recurse {streamInvariantProof = newStreamInvariantProof} next)
    --recurse (Yield {streamInvariantProof} value next) = Yield {oldStreamInvariantProof = streamInvariantProof} value (recurse {streamInvariantProof} next)
    recurse (Yield value next) = Yield value (recurse next)
    recurse (Return value returnInvariantProof) = Return value ()


record ErasedDPair {0 a: Type} {0 b: a -> Type} where
    constructor MkErasedDPair
    0 fst : a
    0 snd : b fst


IsInputExhaustedContainsUpstreamReturnProof :
    --(returnOut: Type)
    (IsInputExhausted -> List streamIn -> List streamOut -> returnOut -> Type)
    -> (historyIn: List streamIn)
    -> (historyOut: List streamOut)
    -> IsInputExhausted
    -> IsInputExhausted
    -> Type
IsInputExhaustedContainsUpstreamReturnProof {-returnOut-} returnInvariant historyIn historyOut isUpstreamInputExhausted No = ()
IsInputExhaustedContainsUpstreamReturnProof {-returnOut-} returnInvariant historyIn historyOut isUpstreamInputExhausted (Yes property _)
    = ErasedDPair
        {a = returnOut}
        {b = \finalReturnOut
            => property = returnInvariant isUpstreamInputExhausted historyIn historyOut finalReturnOut
        }
    --= Exists {type = returnOut} $ \finalReturnOut
    --    => property = returnInvariant isInputExhausted historyIn historyOut finalReturnOut
    --= (finalReturnOut: returnOut
    --    ** property = returnInvariant isInputExhausted historyIn historyOut finalReturnOut)


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


composeReturnInvariants :
    (IsInputExhausted -> List streamIn -> List streamMid -> returnMid -> Type)
    -> (IsInputExhausted -> List streamMid -> List streamOut -> returnOut -> Type)
    -> (IsInputExhausted)
    -> List streamIn
    -> List streamOut
    -> returnOut
    -> Type
composeReturnInvariants
    returnInvariantUpstream
    returnInvariantDownstream
    finalIsInputExhaustedIn
    finalHistoryIn
    finalHistoryOut
    finalReturnOut
    = Exists
        {
            type = (IsInputExhausted, List streamMid)
        }
        $ \(finalIsInputExhaustedMid, finalHistoryMid) => (
            returnInvariantDownstream
                finalIsInputExhaustedMid
                finalHistoryMid
                finalHistoryOut
                finalReturnOut,
            ErasedDPair
                {
                    a = IsInputExhaustedContainsUpstreamReturnProof
                        returnInvariantUpstream
                        finalHistoryIn
                        finalHistoryMid
                        finalIsInputExhaustedIn
                        finalIsInputExhaustedMid
                }
                {
                    b = \finalIsInputExhaustedMidContainsUpstreamReturnProof =>
                        case finalIsInputExhaustedMid of
                            No => ()
                            Yes _ _ =>
                                let finalReturnMid = fst finalIsInputExhaustedMidContainsUpstreamReturnProof in
                                    returnInvariantUpstream
                                        finalIsInputExhaustedIn
                                        finalHistoryIn
                                        finalHistoryMid
                                        finalReturnMid
                }
            --case finalIsInputExhaustedMid of
            --    No => ()
            --    Yes property propertyProof => 

            -- Exists {type = returnMid} $ \finalReturnMid => case finalIsInputExhaustedMid of
            --     No => ()
            --     Yes _ _ =>
            --         returnInvariantUpstream
            --             finalIsInputExhaustedIn
            --             finalHistoryIn
            --             finalHistoryMid
            --             finalReturnMid

            --Exists
            --    {
            --        type = IsInputExhaustedContainsUpstreamReturnProof
            --            returnInvariantUpstream
            --            finalHistoryIn
            --            finalHistoryMid
            --            finalIsInputExhaustedMid
            --    }
            --    $ \(Evidence finalReturnMid _) => case finalIsInputExhaustedMid of
            --        No => ()
            --        Yes _ _ =>
            --            returnInvariantUpstream
            --                finalIsInputExhaustedIn
            --                finalHistoryIn
            --                finalHistoryMid
            --                finalReturnMid
        )


testeq : (y: (x: Type ** x)) -> (Nat = fst y) -> Nat
--testeq (a ** b) c = b
testeq (a ** b) c = rewrite c in b


infixr 9 .|
||| The pipe operator chains two pipes together.
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
            --streamInvariantProof = streamInvariantProofUpstream
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
            --streamInvariantProof = streamInvariantProofDownstream
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
            streamInvariant = NoStreamInvariant, -- Too hard and messy for now, since it's not something that's always satisfied
            --streamInvariant = composeStreamInvariants streamInvariantUpstream streamInvariantDownstream,
            returnInvariant = composeReturnInvariants returnInvariantUpstream returnInvariantDownstream
            --streamInvariantProof = Evidence historyMid (steamInvariantProofUpstream, streamInvariantProofDownstream)
            --returnInvariant = \finalIsInputExhaustedIn, finalHistoryIn, finalReturnOut =>
            --    (finalIsInputExhaustedMid: IsInputExhausted
            --        ** (
            --            finalHistoryMid: List streamMid
            --            ** (
            --                returnInvariantB finalIsInputExhaustedMid finalHistoryMid finalReturnOut,
            --                streamInvariantMid finalHistoryIn finalHistoryMid,
            --                case finalIsInputExhaustedMid of
            --                    No => ()
            --                    Yes _ _ => returnInvariantA finalIsInputExhaustedIn finalHistoryIn finalHistoryMid finalReturnMid -- todo looks like maybe we dont care about IsInputExhausted proofs
            --            )
            --        )
            --    )
        }
        effects
        returnOut
    --newInvariant = \finalHistoryIn, returnValue =>
    --  Exists (List streamMid) \historyMid => 
    --      (returnInvariantB historyMid returnValue, streamInvariantA finalHistoryIn historyMid)
(.|) = pull {midExhaustedContainsUpstreamReturnProof = ()} {-{pullStreamInvariantProofUpstream = ?todobasecase}-} where
    mutual
        pull : 
            Monad effects'
            => {0 pullIsInputExhaustedIn: IsInputExhausted}
            -> {0 pullIsInputExhaustedMid: IsInputExhausted}
            -> {0 pullHistoryIn: List streamIn}
            -> {0 pullHistoryMid: List streamMid}
            ---> {0 streamInvariantProofUpstream: streamInvariantUpstream pullHistoryIn pullHistoryMid}
            ---> {0 streamInvariantProofDownstream: streamInvariantDownstream pullHistoryMid pullHistoryMid}
            ---> {0 pullStreamInvariantProofUpstream: streamInvariantUpstream pullHistoryIn pullHistoryMid}
            ---> {0 pullStreamInvariantProofDownstream: streamInvariantDownstream pullHistoryMid pullHistoryOut}
            -> {0 midExhaustedContainsUpstreamReturnProof:
                IsInputExhaustedContainsUpstreamReturnProof
                    returnInvariantUpstream
                    pullHistoryIn
                    pullHistoryMid
                    pullIsInputExhaustedIn
                    pullIsInputExhaustedMid
            }
            -- -> {0 midExhaustedContainsUpstreamReturnProof: case pullIsInputExhaustedMid of
            --    No => ()
            --    Yes property _ =>
            --        (finalReturnMid: returnMid
            --            ** property = returnInvariantUpstream pullIsInputExhaustedIn pullHistoryIn pullHistoryMid finalReturnMid)
            -- }
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
                    --streamInvariantProof = pullStreamInvariantProofUpstream
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
                    --streamInvariantProof = pullStreamInvariantProofDownstream
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
                    --streamInvariant = composeStreamInvariants streamInvariantUpstream streamInvariantDownstream,
                    streamInvariant = NoStreamInvariant,
                    returnInvariant = composeReturnInvariants returnInvariantUpstream returnInvariantDownstream
                    --streamInvariantProof = Evidence pullHistoryMid (pullStreamInvariantProofUpstream, pullStreamInvariantProofDownstream)
                }
                effects'
                returnOut
        pull upstream (Do action)
            -- {
            --     streamInvariantProofUpstream,
            --     midExhaustedContainsUpstreamReturnProof
            -- }
            = Do (action >>= \nextDownstreamPipe => lazyPure (pull
                {
                    --streamInvariantProofUpstream,
                    midExhaustedContainsUpstreamReturnProof
                }
                upstream
                nextDownstreamPipe
            ))
        pull upstream (Yield {streamInvariantProof = newStreamInvariantProofDownstream} value downstreamNext)
            --  {
            --      streamInvariantProofUpstream,
            --      pullHistoryMid
            --  }
            = Yield
                value
                -- {
                --     streamInvariantProof = Evidence pullHistoryMid (pullStreamInvariantProofUpstream, newStreamInvariantProofDownstream)
                -- }
                (
                    pull
                        {
                            --streamInvariantProofUpstream,
                            midExhaustedContainsUpstreamReturnProof
                        }
                        upstream
                        downstreamNext
                )
        pull upstream (Await downstreamOnReturn downstreamOnStream)
            -- {
            --     streamInvariantProofUpstream,
            --     pullHistoryMid
            -- }
            = push upstream downstreamOnReturn downstreamOnStream
        pull {pullHistoryMid} upstream (Return value returnInvariantProof)
            = Return value (Evidence
                (pullIsInputExhaustedMid, pullHistoryMid)
                (
                    returnInvariantProof,
                    MkErasedDPair
                        midExhaustedContainsUpstreamReturnProof
                        (case pullIsInputExhaustedMid of
                            No => ()
                            Yes upstreamReturnProperty upstreamReturnProof => rewrite sym (snd midExhaustedContainsUpstreamReturnProof) in upstreamReturnProof
                            --Yes upstreamReturnProperty upstreamReturnProof => upstreamReturnProof --where
                            --    finalReturnMid : returnMid
                            --    finalReturnMid = fst midExhaustedContainsUpstreamReturnProof

                            --    upstreamReturnInvariantProof : returnInvariantUpstream pullIsInputExhaustedIn pullHistoryIn pullHistoryMid finalHistoryMid
                            --    upstreamReturnInvariantProof = rewrite snd midExhaustedContainsUpstreamReturnProof in upstreamReturnProof
                            --)
                        )
                        --?todostreamInvariantProofUpstream
                )
            )

        push :
            Monad effects'
            => {0 pushIsInputExhaustedIn: IsInputExhausted}
            -> {0 pushHistoryIn: List streamIn}
            -> {0 pushHistoryMid: List streamMid}
            -- -> {0 streamInvariantProofDownstream: streamInvariantDownstream pushHistoryMid pushHistoryOut}
            ---> {0 pushStreamInvariantProofUpstream: streamInvariantUpstream pushHistoryIn pushHistoryMid}
            ---> {0 pushStreamInvariantProofDownstream: streamInvariantDownstream pushHistoryMid pushHistoryOut}
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
                    --streamInvariantProof = pushStreamInvariantProofUpstream
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
                        --streamInvariantProof = pushStreamInvariantProofDownstream
                    }
                    effects'
                    returnOut
                ))
            -> ((value: streamMid)
                ---> (0 newStreamInvariantProof : streamInvariantDownstream (value :: pushHistoryMid) pushHistoryOut)
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
                        --streamInvariantProof = newStreamInvariantProof
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
                    --streamInvariant = composeStreamInvariants streamInvariantUpstream streamInvariantDownstream,
                    streamInvariant = NoStreamInvariant,
                    returnInvariant = composeReturnInvariants returnInvariantUpstream returnInvariantDownstream
                    --streamInvariantProof = Evidence pushHistoryMid (pushStreamInvariantProofUpstream, pushStreamInvariantProofDownstream)
                }
                effects'
                returnOut
        push (Do action) downstreamOnReturn downstreamOnStream
            = Do (action >>= \nextUpstreamPipe => lazyPure (push nextUpstreamPipe downstreamOnReturn downstreamOnStream))
        --push (Yield {streamInvariantProof = newStreamInvariantProofUpstream} value upstreamNext) downstreamOnReturn downstreamOnStream
            --= pull {pullStreamInvariantProofUpstream = newStreamInvariantProofUpstream} upstreamNext (downstreamOnStream value)
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
            --streamInvariantProof
        }
        effects
        ()
yield {streamInvariantProof} value = Yield value {streamInvariantProof} (Return () ()) -- We set Return () as the initial continuation, which can then be built upon monadically
--yield {streamInvariantProof} value = Yield value {streamInvariantProof} (Return () ()) -- We set Return () as the initial continuation, which can then be built upon monadically
--yield value = Yield value (Return () ()) -- We set Return () as the initial continuation, which can then be built upon monadically


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
-- runPipeWithInvariant (Await _ _) = runPipeWithInvariant $ Await {returnInvariant} absurd (\x => absurd x)
runPipeWithInvariant (Return value {returnInvariantProof}) = pure (Element value returnInvariantProof)


covering
runPipe :
    Monad effects
    => Effect effects return {returnInvariant}
    -> effects return
runPipe pipe = map fst $ runPipeWithInvariant pipe


covering
fromList :
    (Monad effects, Eq streamOut)
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
            returnInvariant = \finalIsInputExhausted, finalHistoryIn, finalHistoryOut, finalReturnOut
                => reverse finalHistoryOut = list
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


--pipeWithListInput :
--    Monad effects
--    => (input: List streamIn)
--    -> Pipe streamIn Void () {historyIn = [], returnInvariant = innerReturnInvariant} effects returnOut
--    -> Effect effects returnOut {returnInvariant = \finalHistoryIn, returnValue => innerReturnInvariant input returnValue}
--pipeWithListInput input pipe = todoInvariantPreservingPipeComposition (fromList input) pipe where
--    todoInvariantPreservingPipeComposition :
--        Monad effects
--        => Pipe Void streamIn Void {historyIn = [], returnInvariant = NoReturnInvariant} effects ()
--        -> Pipe streamIn Void () {historyIn = [], returnInvariant = innerReturnInvariant} effects returnOut
--        -> Effect effects returnOut {returnInvariant = \finalHistoryIn, returnValue => innerReturnInvariant input returnValue}
--    todoInvariantPreservingPipeComposition = ?todoComposeRhs


--covering
--runPurePipeWithList :
--    Pipe streamIn Void () {historyIn = [], returnInvariant} Identity returnOut
--    -> (input: List streamIn)
--    -> Subset returnOut (\returnValue => returnInvariant input returnValue)
--runPurePipeWithList pipe list = ?todoRunPurePipeWithList --runIdentity $ runPipeWithInvariant (todoPipeCompose (fromList list) pipe) where


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
            returnInvariant = \finalIsInputExhausted, finalHistoryIn, finalHistoryOut, finalReturn
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
                returnInvariant = \finalIsInputExhausted, finalHistoryIn, finalHistoryOut, finalReturn
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
                        returnInvariant = \finalIsInputExhausted, finalHistoryIn, finalHistoryOut, finalReturn
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
--splitByEmptyLine initialInnerPipeline = runInnerPipe False initialInnerPipeline where
splitByEmptyLine initialInnerPipeline = runInnerPipe No initialInnerPipeline where
    runInnerPipe :
        --(hasEnded: Bool)
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
                --isInputExhausted = if hasEnded then Yes () () else No,
                historyIn = outerHistoryIn,
                historyOut = outerHistoryOut,
                returnInvariant = NoReturnInvariant
            }
            effects
            ()
    runInnerPipe hasEnded (Do action) = Do (action >>= \nextInnerPipe
        => lazyPure (runInnerPipe hasEnded nextInnerPipe)
        --=> lazyPure (runInnerPipe hasEnded ?todonextinnerpipe)
        --=> ?todosplitdoaction--lazyPure (runInnerPipe hasEnded nextInnerPipe)
        )
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
            --then Return () ()
            --else ?todosplitreturn--runInnerPipe No initialInnerPipeline


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
            returnInvariant = \finalIsInputExhausted, finalHistoryIn, finalHistoryOut, finalReturn
                => finalReturn = foldr (+) 0 finalHistoryIn
        }
        effects
        Nat
sum = fromPurePipe $ foldPipe (+) 0


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
            returnInvariant = \finalIsInputExhausted, finalHistoryIn, finalHistoryOut, finalReturn
                => finalReturn = foldr Data.Nat.maximum 0 finalHistoryIn
        }
        effects
        Nat
max = fromPurePipe $ foldPipe maximum 0


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