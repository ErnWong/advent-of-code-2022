||| VerifiedSewage is a stream processing library that provides functionality
||| similar to iterators in other languages. A piece of computation is
||| modelled as a stream of values that are generated, processed, and consumed
||| by computational units called "Pipes". Pipes can be connected in chains
||| where data produced by an upstream pipe would flow down to the downstream
||| pipe. More importantly, the stream is demand-driven, meaning that the
||| flow of data is controlled downstream, so that upstream will never need to
||| produce more data than it will ever be consumed downstream.
|||
||| This Pipes implementation is based on https://github.com/QuentinDuval/IdrisPipes/
||| but ported from Idris v1 to Idris v2, and heavily extended so that we can prove
||| things about our pipes.
|||
||| I was hoping that I could achieve something similar to this with just
||| using codata or something, as the key part of this is the laziness.
||| However, I haven't figured out how to create a lazily generated stream
||| of data that requires effects to obtain said data or to consume said data,
||| and still be able to process this data in a pure context.
|||
||| The typical usage is to define small modular `Pipe` instances, and
||| wire them together using the pipe composition infix operator `(.|)`.
||| Then, you can run this pipe using `runPipe` which will service the
||| most downstream pipe until it terminates by returning a value.
module VerifiedSewage

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

import Basics


-- Halting problem go brrr...
%default total


||| Here we define a datatype (similar to that of Rust's tagged unions) that
||| describe whether a pipe has exhausted all of its upstream's data, and
||| therefore can no longer pull/await any more data. The upstream is said
||| to be exhausted once the downstream receives a return value from the
||| upstream pipe.
public export
data IsInputExhausted : Type where
    ||| Upstream hasn't been exhausted yet, meaning the pipe is allowed to
    ||| await for more data from upstream.
    No : IsInputExhausted

    ||| Upstream has been exhausted (an optionally here we also supply a proof
    ||| that the upstream did indeed give us a return value). This menas that
    ||| this pipe cannot await for any more data.
    |||
    ||| Alternatively, we can specify that a pipe will never await for stream
    ||| input by specifying that a pipe has its inputs exhausted. Such pipes
    ||| can be used in contexts that expect a non-exhausted pipe by using
    ||| the `fromInputExhaustedPipe` function.
    |||
    ||| @ upstreamReturnProperty describes what type the return proof is going
    |||   to be. In cases where we don't care about passing proofs, we can
    |||   specify the unit type `()` for this argument.
    ||| @ upstreamReturnProof allows information about the upstream return value
    |||   to be propagated downstream. In cases where we don't care about proofs,
    |||   the unit value `()` can be specified for this argument.
    Yes : (0 upstreamReturnProperty : Type) -> (0 upstreamReturnProof : upstreamReturnProperty) -> IsInputExhausted


||| We prove that the two possible `IsInputExhausted` states are mutually
||| exclusive, meaning that if we managed to obtain a proof that they are
||| equal, then we have arrived at a contradiction (aka `Void`).
public export
noIsNeverYes : (No = Yes _ _) -> Void
noIsNeverYes Refl impossible


||| We can talk about how a pipe is guaranteed to only output stream values
||| that satisfy some kind of property, and we do this by specifying
||| "stream invariants", but in cases where we don't care about what invariants
||| a pipe has, we can specify this `NoStreamInvariant` instead, which is
||| always guaranteed to be satisfiable.
|||
||| See the `streamInvariant` type index for the `Pipe` type.
|||
||| @ historyIn The list of stream values that the pipe has seen so far.
||| @ historyOut The list of stream values that the pipe has outputted.
||| The return value is a type that, when we can produce an inhabited value
||| of this type, then we have proven a certain property that relates
||| `historyIn` and `historyOut` together.
public export
NoStreamInvariant : (historyIn : List streamIn) -> (historyOut : List streamOut) -> Type
NoStreamInvariant _ _ = ()


||| We can talk about how a pipe is guaranteed to only output return values
||| that satisfy some kind of property, and we do this by specifying
||| "return invariants", but in cases where we don't care about what invariants
||| a pipe has, we can specify this `NoReturnInvariant` instead, which is
||| always guaranteed to be satisfiable.
|||
||| See the `returnInvariant` type index for the `Pipe` type.
|||
||| @ isInputExhausted Whether or not, by the time the pipe has returned,
|||   that the upstream also returned.
||| @ historyIn The list of stream values the current pipe has received
|||   from upstream by the time the current pipe has returned.
||| @ historyOut The list of stream values the current pipe has outputted
|||   by the time the current pipe has returned.
||| @ returnValue The value that is returned by this pipe.
public export
NoReturnInvariant :
    (isInputExhausted : IsInputExhausted)
    -> (historyIn : List streamIn)
    -> (historyOut : List streamOut)
    -> (returnValue : returnOut)
    -> Type
NoReturnInvariant _ _ _ _ = ()


||| This is a nice convenience function to help build up a pipe's return
||| invariant that guaranttes that, by the the the pipe has returned,
||| the upstream pipe must have been exhausted (aka returned). In other
||| words, a pipe with this invariant guarantees that it will not return
||| earlier than its upstream pipe.
|||
||| For example, to specify a pipe that is guaranteed to read all its
||| upstream input and guaranteed to stream out each value doubled,
||| we can write the following:
|||
||| ```idris
||| Pipe {
|||     returnInvariant = ExhaustsInpuAnd $
|||         \historyIn, historyOut, returnValue =>
|||             historyOut = map (\x => 2 * x) historyIn
||| }
||| ```
|||
||| @ otherReturnInvariant What other return invariants the pipe should
|||   have.
||| @ isInputExhausted Whether or not, by the time the pipe has returned,
|||   that the upstream also returned.
||| @ historyIn The list of stream values the current pipe has received
|||   from upstream by the time the current pipe has returned.
||| @ historyOut The list of stream values the current pipe has outputted
|||   by the time the current pipe has returned.
||| @ returnValue The value that is returned by this pipe.
public export
ExhaustsInputAnd :
    (otherReturnInvariant : List streamIn -> List streamOut -> returnOut -> Type)
    -> (isInputExhausted : IsInputExhausted)
    -> (historyIn : List streamIn)
    -> (historyOut : List streamOut)
    -> (returnValue : returnOut)
    -> Type
ExhaustsInputAnd otherReturnInvariant No _ _ _ = Void
ExhaustsInputAnd otherReturnInvariant (Yes _ _) historyIn historyOut returnValue
    = otherReturnInvariant historyIn historyOut returnValue


||| This is the primary data type for our VerifiedSewage library. A `Pipe`
||| represents the "action" the pipe is performing currently, optionally
||| followed by the next `Pipe` (or instructions on how to obtain that
||| next `Pipe`) that represents the next action after the current action
||| is done. Currently, the four actions a pipe can do are:
|||
|||  1. `Do` - performing some effect, followed by the next pipe state.
|||  2. `Await` - pull data from upstream, which is either followed by
|||     the next pipe state should upstream return its final value,
|||     or followed by the next pipe state should upstream yield
|||     the next stream value.
|||  3. `Yield` - push data downstream, which is followed by
|||     the next pipe state.
|||  4. `Return` - terminate this stream by returning a value, and
|||     ***not*** followed by any subsequent pipe.
|||
||| A `Pipe` can be given a `streamInvariant` and a `returnInvariant`,
||| which describes the properties that must hold when a pipe yields
||| and returns respectively. To enforce these invariants, the pipe
||| must supply proofs for these invariants when yielding or returning
||| a value.
|||
||| Note: At the moment, the `streamInvariant` only holds every time
||| this pipe yields a stream output value, and it's not enforced when
||| awaited a new stream input value. This is because our `streamInvariant`
||| is a bit too free-form: the `streamInvariant` could be imposing
||| some constraints on what input stream values are allowed but in reality
||| an downstream pipe has no control over what an upstream pipe sends
||| downstream (or at least at the moment with this current implementation).
||| It might be possible to fix this by making sure the (.|) operator
||| enforces the downstream's stream invariant by restricting what
||| upstream pipes are allowed.
|||
||| @ streamIn What type of stream values does this pipe expect to receive
|||   from upstream.
||| @ streamOut What type of stream values does this pipe yield.
||| @ returnIn What type of return value does this pipe expect to receive
|||   from upstream.
||| @ isInputExhausted This is a compile-time representation of a piece of
|||   the pipe's runtime state. In particular, this indicates whether the
|||   the current pipe is in a state where the upstream pipe has returned
|||   and therefore the current pipe cannot await for any more values.
||| @ historyIn This is a compile-time representation of a piece of the pipe's
|||   runtime state. In particular, this represents the list of all stream
|||   values it has received from the upstream pipe, in reverse chronological
|||   order (i.e. the most recent value is first in the list).
||| @ historyOut This is a compile-time representation of a piece of the pipe's
|||   runtime state. In particular, this represents the list of all stream
|||   values this pipe has outputted, in reverse chronological order
|||   (i.e. the most recent value is first in the list).
||| @ effects This is the arbitrary container (aka most likely a `Monad`)
|||   in which to perform the effects of this pipe should this pipe decide
|||   to do so (via the `Do` pipe action). An example of a value for this
|||   argument would be the `IO` monad.
||| @ returnOut This is the type that the current pipe is expected to return.
||| @ streamInvariant This is a predicate that relates `historyIn` and `historyOut`,
|||   and is only enforced when the current pipe decides to `Yield` a value.
||| @ returnInvariant This is a predicate that relates `isInputExhausted`,
|||   `historyIn`, `historyOut` and the final return value of this pipe, and
|||   is enforced when the current pipe decides to `Return` a value.
public export
data Pipe :
    (streamIn, streamOut, returnIn : Type)
    -> {0 isInputExhausted : IsInputExhausted} -- TODO: We can pack these into a new PipeState record type
    -> {0 historyIn : List streamIn}
    -> {0 historyOut : List streamOut}
    -> (effects : Type -> Type)
    -> (returnOut : Type)
    -> {default NoStreamInvariant 0 streamInvariant : List streamIn -> List streamOut -> Type}
    -> {default NoReturnInvariant 0 returnInvariant : IsInputExhausted -> List streamIn -> List streamOut -> returnOut -> Type}
    -> Type where

    ||| The `Do` action of a pipe represents some effectful step, such as retrieving
    ||| an input from the user, printing a value, etc. Typically you'd use the `lift`
    ||| function instead of constructing a `Do` value manually, as the `lift` function
    ||| can then be used monadically in a do-block allowing you to ergonomically
    ||| chain the continuation with the ability to extract the value out from this effect.
    |||
    ||| @ effect The effect which, when run, produces the next continuation pipe.
    Do :
        (effect : effects (Inf (Pipe {
            streamIn,
            streamOut,
            returnIn,
            isInputExhausted,
            historyIn,
            historyOut,
            streamInvariant,
            returnInvariant,
            effects,
            returnOut
        })))
        -> Pipe {
            streamIn,
            streamOut,
            returnIn,
            isInputExhausted,
            historyIn,
            historyOut,
            streamInvariant,
            returnInvariant,
            effects,
            returnOut
        }

    ||| The `Yield` action of a pipe represents pushing a stream value downstream.
    ||| Typically you'd use the `yield` function instead of constructing a `Yield`
    ||| value manually, as the `yield` function can then be used monadically in
    ||| a do-block allowing you to ergonomically chain the continuation.
    |||
    ||| @ value The stream value to yield (aka "push") downstream.
    ||| @ streamInvariantProof The proof that this new stream value satisfies the
    |||   stream invariant of this pipe. If `streamInvariant` is `NoStreamInvariant`,
    |||   you can specify the unit value `()` as the proof, although this is an
    |||   `auto` implicit parameter and Idris should be able to deduce it for you in
    |||   most cases.
    ||| @ continuation The next pipe state to run after yielding this `value`.
    Yield :
        (value : streamOut)
        -> {auto 0 streamInvariantProof : streamInvariant historyIn (value :: historyOut)}
        -> (continuation : Inf (Pipe {
            streamIn,
            streamOut,
            returnIn,
            isInputExhausted,
            historyIn,
            historyOut = (value :: historyOut),
            streamInvariant,
            returnInvariant,
            effects,
            returnOut
        }))
        -> Pipe {
            streamIn,
            streamOut,
            returnIn,
            isInputExhausted,
            historyIn,
            historyOut,
            streamInvariant,
            returnInvariant,
            effects,
            returnOut
        }

    ||| The `Await` pipe action transfers control over to the upstream pipe until
    ||| the upstream pipe yields a value or returns a value, in which case
    ||| control transfers back to the current pipe through the corresponding
    ||| continuation pipe. This is effectively "pulling" data from upstream.
    |||
    ||| You can only construct an `Await` pipe action if you can guarantee that
    ||| the pipe currently hasn't exhausted its upstream yet.
    |||
    ||| @ returnContinuation The pipe state to run next if upstream returns.
    |||   The return continuation is given the value that the upstream returned,
    |||   in addition to the proof that this upstream return value satisfies
    |||   upstream's return invariant.
    ||| @ streamContinuation The pipe state to run if upstream yields a value.
    |||   The stream continuation is given the value that the upstream has yielded.
    Await :
        (returnContinuation :
            returnIn
            -> {0 upstreamReturnProperty : Type}
            -> (0 upstreamReturnProof : upstreamReturnProperty)
            -> Inf (Pipe {
                streamIn,
                streamOut,
                returnIn,
                isInputExhausted = Yes upstreamReturnProperty upstreamReturnProof,
                historyIn,
                historyOut,
                streamInvariant,
                returnInvariant,
                effects,
                returnOut
            }))
        -> (streamContinuation :
            (value : streamIn)
            -> Inf (Pipe {
                streamIn,
                streamOut,
                returnIn,
                isInputExhausted = No,
                historyIn = (value :: historyIn),
                historyOut,
                streamInvariant,
                returnInvariant,
                effects ,
                returnOut
            }))
        -> Pipe {
            streamIn,
            streamOut,
            returnIn,
            isInputExhausted = No, -- You can't pull from an exhausted upstream.
            historyIn,
            historyOut,
            streamInvariant,
            returnInvariant,
            effects,
            returnOut
        }

    ||| The `Return` pipe action represents the pipe returning a value to downstream,
    ||| and signifies that the current pipe has terminated and will no longer yield
    ||| any more values.
    |||
    ||| @ returnValue The value to return to downstream.
    ||| @ returnInvariantProof Proof that the current pipe is allowed to return
    |||   at this point in time with `returnValue`.
    Return :
        (returnValue : returnOut)
        -> (0 returnInvariantProof : returnInvariant isInputExhausted historyIn historyOut returnValue)
        -> Pipe {
            streamIn,
            streamOut,
            returnIn,
            isInputExhausted,
            historyIn,
            historyOut,
            streamInvariant,
            returnInvariant,
            effects,
            returnOut
        }


||| Idris's type inference has a very hard time figuring this one out, so we explicitly type it
||| instead of using `pure` directly.
lazyPure :
    Monad effects
    => Inf (Pipe {
        streamIn,
        streamOut,
        returnIn,
        isInputExhausted,
        historyIn,
        historyOut,
        streamInvariant,
        returnInvariant,
        effects,
        returnOut
    })
    -> effects (Inf (Pipe {
        streamIn,
        streamOut,
        returnIn,
        isInputExhausted,
        historyIn,
        historyOut,
        streamInvariant,
        returnInvariant,
        effects,
        returnOut
    }))

lazyPure = pure


||| Transform a pipe by changing what happens instead of returning.
||| This is primarily used to describe a sequence of pipe states
||| in terms of smaller pipes, via our fake monadic bind operator (`>>=`).
|||
||| Note: At this stage, it seems a bit difficult to compose the
||| return invariants together, and so our current implementation
||| for this function only supports pipes that have no return invariants.
|||
||| @ originalPipe The pipe to transform
||| @ mapReturn The function which takes the final return value of the original
|||   pipe and maps it into a different pipe.
covering
recurseToReturn :
    Monad effects
    => (originalPipe: Pipe {
        streamIn,
        streamOut,
        returnIn,
        isInputExhausted = Yes () (),
        historyIn = initialHistoryIn,
        historyOut = initialHistoryOut,
        streamInvariant,
        returnInvariant = NoReturnInvariant,
        effects,
        returnOut = returnOutA
    })
    -> (mapReturn :
        (0 mapHistoryIn : List streamIn)
        -> (0 mapHistoryOut : List streamOut)
        -> returnOutA
        -> Pipe {
            streamIn,
            streamOut,
            returnIn,
            isInputExhausted,
            historyIn = mapHistoryIn,
            historyOut = mapHistoryOut,
            streamInvariant,
            returnInvariant = NoReturnInvariant,
            effects,
            returnOut = returnOutB
        })
    -> Pipe {
        streamIn,
        streamOut,
        returnIn,
        isInputExhausted,
        historyIn = initialHistoryIn,
        historyOut = initialHistoryOut,
        streamInvariant,
        returnInvariant = NoReturnInvariant,
        effects,
        returnOut = returnOutB
    }

recurseToReturn pipe mapReturn = recurse
        {
            historyIn = initialHistoryIn,
            historyOut = initialHistoryOut
        }
        pipe where

    recurse :
        Pipe {
            streamIn,
            streamOut,
            returnIn,
            isInputExhausted = Yes () (),
            historyIn,
            historyOut,
            streamInvariant,
            returnInvariant = NoReturnInvariant,
            effects,
            returnOut = returnOutA
        }
        -> Pipe {
            streamIn,
            streamOut,
            returnIn,
            isInputExhausted,
            historyIn,
            historyOut,
            streamInvariant,
            returnInvariant = NoReturnInvariant,
            effects,
            returnOut = returnOutB
        }

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


||| Constructs a pipe defined as a sequence of running the first pipe, followed
||| by the second pipe given what the first pipe returned. This is our equivalent
||| of the monadic bind operator. Originally, we actually legitimately implemented
||| the `Monad` interface for `Pipe`, but things grew complicated when we started
||| added proofs to it, so it was easier to just implement the `>>=` operator.
|||
||| Typically, you'd use this operator indirectly using do-notation:
|||
||| ```idris
||| overallPipe = do
|||     value <- lift getLine
|||     _ <- yield value
||| ```
|||
||| This would be equivalent to writing it out in full:
|||
||| ```idris
||| overallPipe = (lift getLine) >>= (\value => yield value)
||| ```
|||
||| Or equivalently:
|||
||| ```idris
||| overallPipe = (Do getLine (\value => Return value)) >>= (\value => Yield value (Return ()))
||| ```
|||
||| Or equivalently, without using our `(>>=)` operator:
|||
||| ```idris
||| overallPipe = (Do getLine (\value => Yield value (Return ())))
||| ```
|||
||| Note: At this stage, it seems a bit difficult to compose the
||| return invariants together, and so our current implementation
||| for this function only supports pipes that have no return invariants.
export
covering
(>>=) :
    Monad effects
    => Pipe {
        streamIn,
        streamOut,
        returnIn,
        isInputExhausted = Yes () (),
        historyIn,
        historyOut,
        streamInvariant,
        returnInvariant = NoReturnInvariant,
        effects,
        returnOut = returnMid
    }
    -> (returnMid
        -> {0 newHistoryIn : List streamIn}
        -> {0 newHistoryOut : List streamOut}
        -> Pipe {
            streamIn,
            streamOut,
            returnIn,
            isInputExhausted,
            historyIn = newHistoryIn,
            historyOut = newHistoryOut,
            streamInvariant,
            returnInvariant = NoReturnInvariant,
            effects,
            returnOut
        })
    -> Pipe {
        streamIn,
        streamOut,
        returnIn,
        isInputExhausted,
        historyIn,
        historyOut,
        streamInvariant,
        returnInvariant = NoReturnInvariant,
        effects,
        returnOut
    }
effects >>= function
    = recurseToReturn effects (\mapHistoryIn, mapHistoryOut, value => function value)


||| Constructs a pipe that performs the given effect and immediately returns the value
||| produced by that effect. Useful for chaining a sequence of pipe actions monadically
||| using the `(>>=)` operator or via do-notation. This is an alternative for
||| constructing a `Do` action manually. See `yield`, a similar function but for the
||| `Yield` action instead of `Do`. Also see `(>>=)` for usage examples.
export
lift :
    Monad effects
    => effects returnOut
    -> Pipe streamIn streamOut returnIn {historyIn, returnInvariant = NoReturnInvariant} effects returnOut
lift effects = Do (effects >>= \value => lazyPure (Return value ()))


||| Constructs a pipe that yields a value and immediately returns the unit value `()`.
||| Useful for chaining a sequence of pipe actions monadically using the `(>>=)` operator
||| or via do-notaion. This is an alternative for constructing a `Yield` action manually.
||| See `lift`, a similar function but for the `Do` action instead of `Yield`.
||| Also see `(>>=)` for usage examples.
export
yield :
    (value : streamOut)
    -> {auto 0 streamInvariantProof : streamInvariant historyIn (value :: historyOut)}
    -> Pipe {
        streamIn,
        streamOut,
        returnIn,
        isInputExhausted,
        historyIn,
        historyOut,
        streamInvariant,
        effects,
        returnOut = ()
    }
-- We set Return () as the initial continuation, which can then be built upon monadically
yield {streamInvariantProof} value = Yield value {streamInvariantProof} (Return () ())


||| Allows a pure pipe (i.e. a pipe whose `effects` is the `Identity` monad) to
||| be used in places that uses a different `effects` type.
export
covering
fromPurePipe :
    Monad effects
    => Pipe {
        streamIn,
        streamOut,
        returnIn,
        isInputExhausted = overallIsInputExhausted,
        historyIn = overallHistoryIn,
        historyOut = overallHistoryOut,
        returnInvariant = overallReturnInvariant,
        effects = Identity,
        returnOut
    }
    -> Pipe {
        streamIn,
        streamOut,
        returnIn,
        isInputExhausted = overallIsInputExhausted,
        historyIn = overallHistoryIn,
        historyOut = overallHistoryOut,
        returnInvariant = overallReturnInvariant,
        effects,
        returnOut
    }
fromPurePipe pipe = recurse pipe where
    ||| Recurse, preserving everything about the original pipe, except
    ||| for `Do` actions where we map the original action into
    ||| the equivalent for the given `effects` monad. Since
    ||| the original pipe uses `Identity` for `effects`, we can
    ||| trivially extract the pure value using `runIdentity`.
    recurse :
        Inf (Pipe {
            streamIn,
            streamOut,
            returnIn,
            isInputExhausted = innerIsInputExhausted,
            historyIn = innerHistoryIn,
            historyOut = innerHistoryOut,
            returnInvariant = innerReturnInvariant,
            effects = Identity,
            returnOut
        })
        -> Pipe {
            streamIn,
            streamOut,
            returnIn,
            isInputExhausted = innerIsInputExhausted,
            historyIn = innerHistoryIn,
            historyOut = innerHistoryOut,
            returnInvariant = innerReturnInvariant,
            effects,
            returnOut
        }
    recurse (Do action) = Do (pure (runIdentity action) >>= \next => lazyPure $ recurse next)
    recurse (Yield {streamInvariantProof} value next) = Yield {streamInvariantProof} value (recurse next)
    recurse (Await onReturn onStream) = Await
        (\value, upstreamReturnProof => recurse $ onReturn value upstreamReturnProof)
        (\value => recurse $ onStream value)
    recurse (Return value returnInvariantProof) = Return value returnInvariantProof


||| Allow an input-exhausted pipe to be used in places that don't
||| expect its input to be exhausted yet. This is fine because
||| an input-exhausted pipe just means that it is not allowed
||| to yield anything. However, we will be dropping the original
||| return invariant since that depends on whether the input is
||| exhausted or not.
export
covering
fromInputExhaustedPipe :
    Monad effects
    => Pipe {
        streamIn,
        streamOut,
        returnIn,
        isInputExhausted = Yes upstreamReturnProperty upstreamReturnProof,
        streamInvariant = NoStreamInvariant,
        returnInvariant,
        effects,
        returnOut
    }
    -> Pipe {
        streamIn,
        streamOut,
        returnIn,
        isInputExhausted = No,
        streamInvariant = NoStreamInvariant,
        returnInvariant = NoReturnInvariant, -- original return invariant is not compatible, so we discard it
        effects,
        returnOut
    }
fromInputExhaustedPipe pipe = recurse pipe where
    ||| Trivially recurse through the pipe, preserving everything except
    ||| for changing the type signature and discarding the return proof.
    recurse :
        Pipe {
            streamIn,
            streamOut,
            returnIn,
            isInputExhausted = Yes upstreamReturnProperty upstreamReturnProof,
            streamInvariant = NoStreamInvariant,
            returnInvariant,
            effects,
            returnOut
        }
        -> Pipe {
            streamIn,
            streamOut,
            returnIn,
            isInputExhausted = No,
            streamInvariant = NoStreamInvariant,
            returnInvariant = NoReturnInvariant,
            effects,
            returnOut
        }
    recurse (Do action) = Do (action >>= \next => lazyPure $ recurse next)
    recurse (Yield value next) = Yield value (recurse next)
    recurse (Return value returnInvariantProof) = Return value () -- Discard return proof


||| This is a predicate that shows that a particular `IsInputExhausted` value will be
||| holding the proof for the upstream return invariant once its value is `Yes`.
||| Useful in conjunction with `upstreamReturnProofFromInputExhausted` which allows
||| us to package upstream's return proof into downstream's `isInputExhausted` and
||| then extract it back out when we need it.
IsInputExhaustedContainsUpstreamReturnProof :
    (IsInputExhausted -> List streamIn -> List streamOut -> returnOut -> Type)
    -> (historyIn : List streamIn)
    -> (historyOut : List streamOut)
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


||| Extract the upstream proof from downstream's `isInputExhausted` state.
||| Since the downstream's `isInputExhausted` is free to contain any
||| value of any type, we need additional information `IsInputExhaustedContainsUpstreamProof`
||| to constrain it to a type we wanted before we can extract it back out.
export
0 upstreamReturnProofFromInputExhausted :
    {0 returnInvariant : IsInputExhausted -> List streamIn -> List streamMid -> returnMid -> Type}
    -> {0 historyIn : List streamIn}
    -> {0 historyMid : List streamMid}
    -> {0 isInputExhaustedIn : IsInputExhausted}
    -> (isInputExhaustedMid : IsInputExhausted)
    -> (containsUpstreamReturnProof :
        IsInputExhaustedContainsUpstreamReturnProof
            returnInvariant
            historyIn
            historyMid
            isInputExhaustedIn
            isInputExhaustedMid
    )
    -> (proofThatWeDidExhaust :
        Exists $ \property
            => Exists $ \returnProof
                => (isInputExhaustedMid = Yes property returnProof)
    )
    -> ErasedDPair {
        a = returnMid,
        b = \finalReturnMid => returnInvariant isInputExhaustedIn historyIn historyMid finalReturnMid
    }
upstreamReturnProofFromInputExhausted isInputExhaustedMid@No _ proofThatWeDidExhaust
    = void $ noIsNeverYes $
        (the (No = isInputExhaustedMid) Refl)
        `trans`
        (the (isInputExhaustedMid = Yes _ _) (snd $ snd proofThatWeDidExhaust))
upstreamReturnProofFromInputExhausted (Yes property returnProof) containsUpstreamReturnProof _
    = MkErasedDPair
        (fst containsUpstreamReturnProof)
        (
            rewrite
                the (returnInvariant isInputExhaustedIn historyIn historyMid (fst containsUpstreamReturnProof) = property)
                    $ sym $ snd containsUpstreamReturnProof
            in
                returnProof
        )


||| Compose two stream invariants together. Actually, this is dead code, as we soon found out
||| that we don't have the right information to compose the two just yet, as the
||| stream invariants don't always hold (i.e. they only hold at the moment a pipe yields).
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
||| Compose the return proofs for two pipes. This is also used to compose two return invariants.
||| If an upstream pipe is composed with a downstream pipe via `(.|)`, it means the following:
||| 1. If downstream returned, then we have proof that the downstream invariant is fulfilled.
||| 2. If we also know that the downstream has its input exhausted when downstream returned,
|||    then it follows that we also have the upstream pipe's return proof.
||| In order to talk about the downstream return invariant being fulfilled, it needs to refer
||| to the list of stream values that the downstream had received, but that information is
||| erased when we joined the two pipes together. Therefore, our composed proof talks about
||| "there exists" some `historyMid` for which the downstream invariant is fulfilled. Then,
||| if we happen to also know that the upstream pipe has also returned, we can also impose some
||| further constraints as to what this `historyMid` is.
export
record ComposedReturnProof
    {0 streamIn : Type}
    {0 streamMid : Type}
    {0 returnMid : Type}
    (returnInvariantUpstream : IsInputExhausted -> List streamIn -> List streamMid -> returnMid -> Type)
    (returnInvariantDownstream : IsInputExhausted -> List streamMid -> List streamOut -> returnOut -> Type)
    (isInputExhaustedIn : IsInputExhausted)
    (historyIn : List streamIn)
    (historyOut : List streamOut)
    (returnOutValue : returnOut)
    where
        constructor MkComposedReturnProof
        0 isInputExhaustedMid : IsInputExhausted
        0 historyMid : List streamMid
        0 downstreamProof :
            returnInvariantDownstream
                isInputExhaustedMid
                historyMid
                historyOut
                returnOutValue
        0 midExhaustedContainsUpstreamReturnProof :
            IsInputExhaustedContainsUpstreamReturnProof
                returnInvariantUpstream
                historyIn
                historyMid
                isInputEhaustedIn
                isInputExhaustedMid


infixr 9 .|
||| Operator to compose two pipes together, where the streamOut and returnOut of the upstream pipe flow
||| into the streamIn and returnIn of the downstream pipe, similar to that of Unix streams and pipes.
export
covering --todo totality
(.|) :
    Monad effects
    => Pipe {
        streamIn,
        streamOut = streamMid,
        returnIn,
        isInputExhausted = isInputExhaustedIn,
        historyIn,
        historyOut = historyMid,
        streamInvariant = streamInvariantUpstream,
        returnInvariant = returnInvariantUpstream,
        effects,
        returnOut = returnMid
    }
    -> Pipe {
        streamIn = streamMid,
        streamOut,
        returnIn = returnMid,
        isInputExhausted = No,
        historyIn = historyMid,
        historyOut,
        streamInvariant = streamInvariantDownstream,
        returnInvariant = returnInvariantDownstream,
        effects,
        returnOut
    }
    -> Pipe {
        streamIn,
        streamOut,
        returnIn,
        isInputExhausted = isInputExhaustedIn,
        historyIn,
        historyOut,
        -- It's too hard and messy for now to compose two stream invariants together,
        -- since it's not something that's always satisfied (i.e. we don't enforce it when
        -- a pipe awaits a new value, so the stream invariant could be broken at that point).
        streamInvariant = NoStreamInvariant,
        returnInvariant = ComposedReturnProof returnInvariantUpstream returnInvariantDownstream,
        effects,
        returnOut
    }
-- The composed pipe starts with the downstream having control.
(.|) = pull {midExhaustedContainsUpstreamReturnProof = ()} where
    mutual
        ||| Service the downstream pipe until it `Await`s for the upstream.
        pull : 
            Monad effects'
            => {0 pullIsInputExhaustedIn : IsInputExhausted}
            -> {0 pullIsInputExhaustedMid : IsInputExhausted}
            -> {0 pullHistoryIn : List streamIn}
            -> {0 pullHistoryMid : List streamMid}
            -> {0 midExhaustedContainsUpstreamReturnProof :
                IsInputExhaustedContainsUpstreamReturnProof
                    returnInvariantUpstream
                    pullHistoryIn
                    pullHistoryMid
                    pullIsInputExhaustedIn
                    pullIsInputExhaustedMid
            }
            -> Pipe {
                streamIn,
                streamOut = streamMid,
                returnIn,
                isInputExhausted = pullIsInputExhaustedIn,
                historyIn = pullHistoryIn,
                historyOut = pullHistoryMid,
                streamInvariant = streamInvariantUpstream,
                returnInvariant = returnInvariantUpstream,
                effects = effects',
                returnOut = returnMid
            }
            -> Pipe {
                streamIn = streamMid,
                streamOut,
                returnIn = returnMid,
                isInputExhausted = pullIsInputExhaustedMid,
                historyIn = pullHistoryMid,
                historyOut = pullHistoryOut,
                streamInvariant = streamInvariantDownstream,
                returnInvariant = returnInvariantDownstream,
                effects = effects',
                returnOut
            }
            -> Pipe {
                streamIn,
                streamOut,
                returnIn,
                isInputExhausted = pullIsInputExhaustedIn,
                historyIn = pullHistoryIn,
                historyOut = pullHistoryOut,
                streamInvariant = NoStreamInvariant,
                returnInvariant = ComposedReturnProof returnInvariantUpstream returnInvariantDownstream,
                effects = effects',
                returnOut
            }
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

        ||| Service the upstream pipe until it `Yield`s a value back to downstream.
        push :
            Monad effects'
            => {0 pushIsInputExhaustedIn : IsInputExhausted}
            -> {0 pushHistoryIn : List streamIn}
            -> {0 pushHistoryMid : List streamMid}
            -> Pipe {
                streamIn,
                streamOut = streamMid,
                returnIn,
                isInputExhausted = pushIsInputExhaustedIn,
                historyIn = pushHistoryIn,
                historyOut = pushHistoryMid,
                streamInvariant = streamInvariantUpstream,
                returnInvariant = returnInvariantUpstream,
                effects = effects',
                returnOut = returnMid
            }
            -> (returnMid
                -> {0 upstreamReturnProperty : Type}
                -> (0 upstreamReturnProof : upstreamReturnProperty)
                -> Inf (Pipe {
                    streamIn = streamMid,
                    streamOut,
                    returnIn = returnMid,
                    isInputExhausted = Yes upstreamReturnProperty upstreamReturnProof,
                    historyIn = pushHistoryMid,
                    historyOut = pushHistoryOut,
                    streamInvariant = streamInvariantDownstream,
                    returnInvariant = returnInvariantDownstream,
                    effects = effects',
                    returnOut
                })
            )
            -> ((value : streamMid)
                -> Inf (Pipe {
                    streamIn = streamMid,
                    streamOut,
                    returnIn = returnMid,
                    isInputExhausted = No,
                    historyIn = value :: pushHistoryMid,
                    historyOut = pushHistoryOut,
                    streamInvariant = streamInvariantDownstream,
                    returnInvariant = returnInvariantDownstream,
                    effects = effects',
                    returnOut
                })
            )
            -> Pipe {
                streamIn,
                streamOut,
                returnIn,
                isInputExhausted = pushIsInputExhaustedIn,
                historyIn = pushHistoryIn,
                historyOut = pushHistoryOut,
                streamInvariant = NoStreamInvariant,
                returnInvariant = ComposedReturnProof returnInvariantUpstream returnInvariantDownstream,
                effects = effects',
                returnOut
            }
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

                    -- Package our upstream return proof into `pullIsInputExhaustedMid`,
                    -- and also carry a proof that this `IsInputExhausted` does indeed
                    -- contain the upstream return proof so we can later extract it
                    -- back out when the downstream also returns.
                    pullIsInputExhaustedMid = Yes _ returnInvariantProof,
                    midExhaustedContainsUpstreamReturnProof = MkErasedDPair value Refl
                }
                (Return value returnInvariantProof)
                (downstreamOnReturn value returnInvariantProof)


||| An `Effect` is a `Pipe` that doesn't receive any stream or return inputs,
||| nor yields any stream outputs. It only returns a value after performing
||| some effects.
|||
||| This is typically the end result after composing various pipes together.
||| It means that we have paired all consumer pipes with producer pipes, and
||| so we are ready to run the pipe with `runPipe`.
public export
Effect :
    (effects : Type -> Type)
    -> (returnOut : Type)
    -> {default NoReturnInvariant 0 returnInvariant :
        IsInputExhausted -> List Void -> List Void -> returnOut -> Type} -> Type
Effect effects returnOut = Pipe {
    streamIn = Void, -- An effect pipe doesn't take any stream in
    streamOut = Void, -- nor does it stream anything out,
    returnIn = Void, -- nor does it accepts any upstream return value
    isInputExhausted = Yes () (), -- and nevers awaits any upstream for input
    historyIn = [],
    historyOut = [],
    returnInvariant,
    effects,
    returnOut -- but it can return something itself
}


||| This is a more type-rich version of `runPipe` which runs a pipe until it returns a value.
||| Not only does this function return the final return value of a pipe, but it also provides
||| a proof that the final return invariant is fulfilled.
|||
||| See also `runPurePipeWithList` and `runInputExhaustingPurePipeWithList`.
export
covering
runPipeWithInvariant :
    Monad effects
    => Effect effects return {returnInvariant}
    -> effects (Subset return (\returnValue => returnInvariant (Yes () ()) [] [] returnValue))
runPipeWithInvariant (Do action) = action >>= \nextPipe => runPipeWithInvariant nextPipe
runPipeWithInvariant (Yield value _) = absurd value
runPipeWithInvariant (Return value {returnInvariantProof}) = pure (Element value returnInvariantProof)


||| Run a pipe until it returns a value, potentially performing effects in the process.
|||
||| See `runPipeWithInvariant` if you want to extract out the return invariant proof as well
||| as the return value.
|||
||| See also `runPurePipeWithList` and `runInputExhaustingPurePipeWithList`.
export
covering
runPipe :
    Monad effects
    => Effect effects return {returnInvariant}
    -> effects return
runPipe pipe = map fst $ runPipeWithInvariant pipe


||| The return invariant for the `fromList` pipe, extracted out as its own top-level definition
||| so we can refer back to it in multiple places.
fromList_returnInvariant : List streamOut -> IsInputExhausted -> List Void -> List streamOut -> () -> Type
fromList_returnInvariant list _ _ finalHistoryOut _ = reverse finalHistoryOut = list


||| Given a `list`, creates a `Pipe` that streams out the contents of that `list`.
||| Once the `list` is exhausted, the pipe returns the unit value `()`.
export
covering
fromList :
    Monad effects
    => (list : List streamOut)
    -> Pipe {
        streamIn = Void,
        streamOut,
        returnIn = Void,
        isInputExhausted = Yes () (), -- This pipe is guaranteed to not await for any upstream value.
        historyIn = [],
        historyOut = [],
        streamInvariant = \currentHistoryIn, currentHistoryOut
            => (suffix : List streamOut ** (reverse currentHistoryOut) ++ suffix = list),
        returnInvariant = fromList_returnInvariant list,
        effects,
        returnOut = () -- This pipe returns () upon reaching the end of the list.
    }
fromList list = recurse list proofBaseCase where
    proofBaseCase : list = list
    proofBaseCase = Refl

    recurse :
        (remaining : List streamOut)
        -> (0 inductionHypothesis : (reverse historyOut) ++ remaining = list)
        -> Pipe {
            streamIn = Void,
            streamOut,
            returnIn = Void,
            historyOut,
            streamInvariant = \currentHistoryIn, currentHistoryOut
                => (suffix : List streamOut ** (reverse currentHistoryOut) ++ suffix = list),
            returnInvariant = \finalIsInputExhausted, finalHistoryIn, finalHistoryOut, finalReturnOut
                => reverse finalHistoryOut = list,
            effects,
            returnOut = ()
        }

    recurse [] historyIsPrefix = Return () {returnInvariantProof = hypothesisRearranged} where
        0 inductionHypothesis : (reverse historyOut) ++ [] = list
        inductionHypothesis = historyIsPrefix

        0 hypothesisRearranged : reverse historyOut = list
        hypothesisRearranged = rewrite reverseOntoSpec [] historyOut in inductionHypothesis

    recurse (x :: xs) historyIsPrefix =
        Yield x
            {streamInvariantProof = (xs ** inductionStep)}
            (recurse xs inductionStep) where
                0 inductionHypothesis : (reverse historyOut) ++ (x :: xs) = list
                inductionHypothesis = historyIsPrefix

                0 hypothesisRearranged : ((reverse historyOut) ++ [x]) ++ xs = list
                hypothesisRearranged = rewrite sym (appendAssociative (reverse historyOut) [x] xs) in inductionHypothesis

                0 inductionStep : (reverse (x :: historyOut)) ++ xs = list
                inductionStep = rewrite reverseMovesHeadToEnd x historyOut in hypothesisRearranged


||| Runs a pipe just like `runPipe` and `runPipeWithInvariant`, except that it feeds the given
||| pipe with a predefined list of stream input values.
|||
||| See `runInputExhaustingPurePipeWithList` for a stronger version of this function.
export
covering
runPurePipeWithList :
    Pipe {
        streamIn,
        streamOut = Void,
        returnIn = (),
        isInputExhausted = No,
        historyIn = [],
        historyOut = [],
        returnInvariant,
        effects = Identity,
        returnOut
    }
    -> (input : List streamIn)
    -> Subset returnOut $
        \returnValue
            => ComposedReturnProof
                {
                    streamIn = Void,
                    returnMid = ()
                }
                (fromList_returnInvariant input)
                returnInvariant
                (Yes () ())
                []
                []
                returnValue
runPurePipeWithList pipe list = runIdentity $ runPipeWithInvariant $ fromList list .| pipe


||| Runs a pipe with a given list just like `runPurePipeWithList`, but with the further
||| restriction that the given pipe must consume all of the list.
export
covering
runInputExhaustingPurePipeWithList :
    Pipe {
        streamIn,
        streamOut = Void,
        returnIn = (),
        isInputExhausted = No,
        historyIn = [],
        historyOut = [],
        returnInvariant = ExhaustsInputAnd returnInvariant,
        effects = Identity,
        returnOut
    }
    -> (input : List streamIn)
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
            (isInputExhausted : IsInputExhausted)
            -> Either
                (isInputExhausted = No)
                (Exists {type = Type} $ \a
                    => Exists {type = a} $ \b
                        => isInputExhausted = Yes a b)
        extractIsInputExhaustedEquality No = Left Refl
        extractIsInputExhaustedEquality (Yes a b) = Right (Evidence a $ Evidence b Refl)

        0 midIsExhausted : 
            (Exists {type = Type} $ \a
                => Exists {type = a} $ \b
                    => proofs.isInputExhaustedMid = Yes a b)
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
        proofThatReverseOfHistoryMidEqualsList = snd $
            upstreamReturnProofFromInputExhausted
                proofs.isInputExhaustedMid
                proofs.midExhaustedContainsUpstreamReturnProof
                midIsExhausted

        0 proofThatHistoryMidEqualsReverseOfList : proofs.historyMid = reverse list
        proofThatHistoryMidEqualsReverseOfList
            = reverseCanJumpAcrossTheEqualsSign proofs.historyMid list proofThatReverseOfHistoryMidEqualsList

        0 finalProof : returnInvariant (reverse list) [] returnValue
        finalProof = rewrite sym proofThatHistoryMidEqualsReverseOfList in downstreamReturnInvariantProof
    in
        Element returnValue finalProof


||| Creates a pipe that uses the given map function to map each individualy
||| stream value it receives from upstream before yielding the result downstream.
export
covering
mapEach :
    Monad effects
    => (streamIn -> streamOut)
    -> Pipe {
        streamIn,
        streamOut,
        returnIn,
        isInputExhausted = No,
        effects,
        returnOut = returnIn
    }
mapEach function = Await  
    (\returnValue, returnProof => Return returnValue ())
    (\streamValue => do
        _ <- yield (function streamValue)
        mapEach function
    )


||| Creates a pipe that folds the stream input down into a single return value.
export
covering --todo
foldPipe :
    (reducer : streamIn -> returnOut -> returnOut)
    -> (initialValue : returnOut)
    -> Pipe {
        streamIn,
        streamOut = Void,
        returnIn = (),
        isInputExhausted = No,
        historyIn = [],
        historyOut = [],
        returnInvariant = ExhaustsInputAnd $ \finalHistoryIn, finalHistoryOut, finalReturn
            => finalReturn = foldr reducer initialValue finalHistoryIn,
        effects = Identity,
        returnOut
    }

foldPipe reducer initialValue = recurse [] initialValue proofBaseCase where
    proofBaseCase : initialValue = foldr reducer initialValue []
    proofBaseCase = Refl

    recurse :
        (0 historyIn : List streamIn)
        -> (accumulator : returnOut)
        -> (0 inductionHypothesis : accumulator = foldr reducer initialValue historyIn)
        -> Pipe {
            streamIn,
            streamOut = Void,
            returnIn = (),
            isInputExhausted = No,
            historyIn,
            historyOut = [],
            returnInvariant = ExhaustsInputAnd $ \finalHistoryIn, finalHistoryOut, finalReturn
                => finalReturn = foldr reducer initialValue finalHistoryIn,
            effects = Identity,
            returnOut
        }

    recurse historyIn accumulator proofThatAccumulatorEqualsFoldr =
        Await
            (\returnValue, returnProof => Return accumulator proofThatAccumulatorEqualsFoldr)
            onStream
        where
            onStream :
                (value : streamIn)
                -> Inf (Pipe {
                    streamIn,
                    streamOut = Void,
                    returnIn = (),
                    isInputExhausted = No,
                    historyIn = (value :: historyIn),
                    historyOut = [],
                    returnInvariant = ExhaustsInputAnd $ \finalHistoryIn, finalHistoryOut, finalReturn
                        => finalReturn = foldr reducer initialValue finalHistoryIn,
                    effects = Identity,
                    returnOut
                })
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


||| A pipe that reads from stdin line by line until reaching EOF.
export
covering
readLines : Has [FileIO, Console] effects => Pipe {
    streamIn = Void,
    streamOut = String,
    returnIn = Void,
    historyIn = [],
    effects = App effects,
    returnOut = ()
}
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


||| A pipe that prints each showable value line by line to stdout.
export
covering
printEach :
    (Show streamValue, Has [Console] effects)
    => Pipe {
        streamIn = streamValue,
        streamOut = streamValue,
        returnIn = (),
        isInputExhausted = No,
        historyIn = [],
        effects = App effects,
        returnOut = ()
    }
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


||| A pipe that lazily groups the input using an empty string as a delimiter, and for each
||| group, it sends the input values to the given inner pipe for it to reduce down to a single
||| return value which the outer pipe uses as a stream value.
|||
||| E.g., if the input was: "1", "2", "3", "", "4", "5", "", "6", then this pipe will stream out
||| the return value of running the inner pipe with "1", "2", "3", then the return value of
||| running the inner pipe with "4", "5", and finally the return value of running the inner
||| pipe with "6".
export
covering
splitByEmptyLine :
    Monad effects
    => Pipe {
        streamIn = String,
        streamOut = Void,
        returnIn = (),
        isInputExhausted = No,
        historyIn = [],
        returnInvariant,
        effects,
        returnOut = splitReturnOut
    }
    -> Pipe {
        streamIn = String,
        streamOut = splitReturnOut,
        returnIn = (),
        isInputExhausted = No,
        historyIn = [],
        returnInvariant = NoReturnInvariant,
        effects,
        returnOut = ()
    }
splitByEmptyLine initialInnerPipeline = runInnerPipe No initialInnerPipeline where
    runInnerPipe :
        (isInputExhausted : IsInputExhausted)
        -> Pipe {
            streamIn = String,
            streamOut = Void,
            returnIn = (),
            isInputExhausted,
            historyIn = innerHistoryIn,
            historyOut = innerHistoryOut,

            -- Allow the inner return invariant to change as we could be dropping it
            returnInvariant = innerReturnInvariant,

            effects,
            returnOut = splitReturnOut
        }
        -> Pipe {
            streamIn = String,
            streamOut = splitReturnOut,
            returnIn = (),
            isInputExhausted,
            historyIn = outerHistoryIn,
            historyOut = outerHistoryOut,
            returnInvariant = NoReturnInvariant,
            effects,
            returnOut = ()
        }
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


||| A pipe that takes a stream of strings and converts it to a stream of natural numbers.
export
covering
parseNat : Monad effects => Pipe {
    streamIn = String,
    streamOut = Nat,
    returnIn = return,
    isInputExhausted = No,
    historyIn = [],
    effects,
    returnOut = return
}
parseNat = mapEach stringToNatOrZ


||| The return invariant for the `sum` pipe.
public export
sum_returnInvariant : List Nat -> List Void -> Nat -> Type
sum_returnInvariant finalHistoryIn finalHistoryOut finalReturn
    = (finalReturn = foldr (+) 0 finalHistoryIn)


||| A pipe that takes a stream of natural numbers and adds them up.
export
covering
sum :
    Monad effects
    => Pipe {
        streamIn = Nat,
        streamOut = Void,
        returnIn = (),
        isInputExhausted = No,
        historyIn = [],
        historyOut = [],
        returnInvariant = ExhaustsInputAnd VerifiedSewage.sum_returnInvariant,
        effects,
        returnOut = Nat
    }
sum = fromPurePipe $ foldPipe (+) 0


||| The return invariant for the `max` pipe.
public export
max_returnInvariant : List Nat -> List Void -> Nat -> Type
max_returnInvariant finalHistoryIn finalHistoryOut finalReturn
    = (finalReturn = foldr Data.Nat.maximum 0 finalHistoryIn)


||| A pipe that takes a stream of natural numbers and returns the maximum number it has seen.
export
covering
max :
    Monad effects
    => Pipe {
        streamIn = Nat,
        streamOut = Void,
        returnIn = (),
        isInputExhausted = No,
        historyIn = [],
        historyOut = [],
        returnInvariant = ExhaustsInputAnd VerifiedSewage.max_returnInvariant,
        effects,
        returnOut = Nat
    }
max = fromPurePipe $ foldPipe maximum 0


||| A pipe that prints the return value of the upstream pipe to stdout.
export
printReturnValue :
    (Show return, Has [Console] effects)
    => Pipe {
        streamIn = Void,
        streamOut = Void,
        returnIn = return,
        isInputExhausted = No,
        historyIn = [],
        effects = App effects,
        returnOut = ()
    }
printReturnValue = recurse where
    recurse : Pipe Void Void return {isInputExhausted = No} (App effects) ()
    recurse = Await
        (\returnValue, returnProof => lift $ putStrLn (show returnValue))
        (\_ => recurse)
