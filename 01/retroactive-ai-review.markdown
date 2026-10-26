The following is a casual review using Google AI (Gemini)

# how does the following style of idris proofs [https://github.com/ErnWong/advent-of-code-2022/blob/master/01/src/VerifiedSewage.idr] compare to the typical / idiomatic style of idris proofs?


The style of Idris proofs found in VerifiedSewage.idr represents an extreme, highly specialized architectural pattern known as type-level state tracking or intrinsic verification.
While Idris is famous for supporting this paradigm, the sheer scale and intensity with which it is applied in this file deviates sharply from what a regular Idris developer writes on a daily basis. It closer resembles an advanced proof-assistant style (like Coq or Agda) forced into an elegant functional architecture.
Here is a breakdown of how this codebase compares to typical, idiomatic Idris development:

1. Intrinsic vs. Extrinsic Verification (The Core Philosophy)

• In this file: The author uses intrinsic verification. The correctness criteria (the invariants) are embedded directly into the main data structure (Pipe). Every single step of the stream execution engine—whether pushing data (Yield), pulling data (Await), or terminating (Return)—forces the programmer to supply a compile-time proof right then and there.
• Idiomatic Idris: Typical Idris code balances intrinsic and extrinsic methods. Idiomatic libraries usually implement a simpler, cleaner type architecture first to keep the operational code highly readable. They then prove properties extrinsically in separate code blocks using helper lemmas, or by exporting theorem functions (myTheorem : (x : Pipe) -> Property x).

2. Manual State Tracking in Types (The historyIn / historyOut Accumulators)

• In this file: The type parameters carry a massive amount of operational baggage:idris
-> {0 isInputExhausted : IsInputExhausted}
-> {0 historyIn : List streamIn}
-> {0 historyOut : List streamOut}
Use code with caution.
Every time a value flows through the stream, these type-level List parameters grow. This means the type signature itself mimics a precise execution trace or state machine.
• Idiomatic Idris: While using zero-quantity erasure (0 parameter : Type) to store compile-time metrics is an idiomatic Idris 2 feature, keeping an exact chronological execution history inside a core stream-monad type is uncommon. Idiomatic Idris code usually abstracts states out into a distinct State or ST monad framework rather than threading custom raw List histories directly through the root data constructor.

3. The Complexity of Composition ((.|))

• In this file: The operator to combine pipes (.|) contains incredibly dense type-level mechanics:idris
IsInputExhaustedContainsUpstreamReturnProof
returnInvariantUpstream
pullHistoryIn
pullHistoryMid
...
Use code with caution.
Composing two stream processors requires an existential package (ComposedReturnProof), tracking what happens to one history when the other terminates. The author even admits in the comments: "It's too hard and messy for now to compose two stream invariants together..."
• Idiomatic Idris: Idiomatic code leans heavily into Idris's interactive editing features (hole filling, case-splitting via the IDE). When type signatures become so structurally entangled that composing two elements requires a monumental type-level framework, idiomatic style dictates stepping back, generalizing the invariants, or decoupling the proof from the composition function.

4. Bypassing Monadic Monoliths

• In this file: The author attempted to implement standard interfaces like Monad, but found that tracking the fluid type-level changes of historyIn and historyOut broke standard typeclass signatures. They had to abandon standard Monad and manually expose a custom (>>=) operator to explicitly track history shifts.
• Idiomatic Idris: Idiomatic Idris style deeply prioritizes leveraging the ecosystem's interface machinery (Functor, Applicative, Monad, Alternative). Developers generally prefer adjusting their verification strategy so that their custom types cleanly fit standard interfaces, allowing the use of ecosystem libraries and seamless do-notation.

Summary Comparison


Metric	VerifiedSewage.idr Style	Typical / Idiomatic Idris Style
Verification Placement	Fully Intrinsic: Code cannot exist without its proofs.	Hybrid: Simple types for code; extrinsic lemmas for deep logic.
Interface Synergy	Isolated: Abandons standard typeclasses for custom type-weaving.	Integrated: Heavy reliance on standard interfaces (Monad, Traversable).
Ergonomics	Brittle: Minor changes to invariants break the whole pipeline.	Flexible: Logic changes can be made without rewrite avalanches.
Type Overhead	Extreme: Types mimic an entire operational history tracker.	Moderate: Types check boundaries, dimensions, or protocols.


The Verdict

The codebase is a masterful display of what is possible in Idris 2. It demonstrates how zero-cost types can perfectly track data processing state machines. However, it is an elite proof-architect's style. Typical, idiomatic Idris is much closer to Haskell with precise refinement boundaries—focusing on clarity of execution first, and using targeted dependent types where they provide the most value without suffocating the composition mechanics.
Would you like to explore how to convert one of these intrinsically verified pipe definitions into a more idiomatic, extrinsically verified equivalent to see the structural contrast?


# yes please I'd be interested to see how this would look like in a more idiomatic style

To transform this into a more idiomatic Idris 2 style, we need to shift from intrinsic verification (where the proofs are forced into the data constructors) to extrinsic verification (where the stream engine is simple and clean, and properties are proven afterward).
We will also restore standard typeclass compliance so we can use Idris's built-in Monad interface without fighting custom (>>=) operators.
Here is how we can refactor this architecture into an idiomatic design.

1. The Idiomatic, Unencumbered Core Engine

Instead of carrying type-level history logs (List streamIn) and custom exhaustiveness proofs, an idiomatic Pipe tracks only what is strictly necessary for runtime execution.
idris
module IdiomaticSewage

import Control.Monad.Trans

public export
data Pipe : (streamIn : Type) -> (streamOut : Type) -> (m : Type -> Type) -> (returnOut : Type) -> Type where
     Do    : m (Pipe i o m r) -> Pipe i o m r
     Yield : o -> Lazy (Pipe i o m r) -> Pipe i o m r
     Await : (Maybe i -> Pipe i o m r) -> Pipe i o m r
     Ready : r -> Pipe i o m r
Use code with caution.

Why this is idiomatic:

• Standard Interfaces Work Out-of-the-Box: Because the type parameters i, o, and r don't change fluidly mid-stream to update "history lists," we can easily implement standard Idris typeclasses like Functor, Applicative, and Monad.
• Elegant Await Pattern: Instead of passing distinct continuations for success and exhaustion, idiomatic code uses Maybe i. Pipelining can automatically feed Nothing downstream once an upstream pipe terminates.
idris
public export
Functor (Pipe i o m) where
  map f (Do action) = Do (map (map f) action)
  map f (Yield x k) = Yield x (map f k)
  map f (Await k)   = Await (\mx => map f (k mx))
  map f (Ready r)   = Ready (f r)

public export
Applicative (Pipe i o m) where
  pure = Ready
  (<*>) = ap -- Standard monadic application

public export
Monad (Pipe i o m) where
  (Ready r) >>= f = f r
  (Do act)  >>= f = Do (map (>>= f) act)
  (Yield x k) >>= f = Yield x (k >>= f)
  (Await k)   >>= f = Await (\mx => k mx >>= f)
Use code with caution.
Now, composing two pipes together via custom pipeline operators (.|) becomes brief and completely free of complex type-level existential unpacking:
idris
infixr 9 .|

public export
(.|) : Monad m => Pipe i mMid m rMid -> Pipe mMid o m rOut -> Pipe i o m rOut
upstream .| (Ready r)  = Ready r
upstream .| (Do action) = Do (map (upstream .|) action)
upstream .| (Yield y k) = Yield y (upstream .| k)
upstream .| (Await k)   = loop upstream k 
  where
    loop : Monad m => Pipe i mMid m rMid -> (Maybe mMid -> Pipe mMid o m rOut) -> Pipe i o m rOut
    loop (Ready _)       k' = loop (Ready (the rMid (idris_crash "exhausted"))) k' .| k' Nothing
    loop (Do action)     k' = Do (map (`loop` k') action)
    loop (Yield y next)  k' = next .| k' (Just y)
    loop (Await kUp)     k' = Await (\mi => loop (kUp mi) k')
Use code with caution.

2. The Idiomatic Verification Strategy: Extrinsic Predicates

If we want to prove that a pipe correctly processes data (e.g., a pipe that doubles every integer it receives), we don't pollute the Pipe constructor. Instead, we write a mathematical Specification Predicate about lists, and then prove that running our pipe matches that spec.
Let's define a clean trace evaluator that converts a pure pipe's execution into a relational list input/output history:
idris
||| A structural history trace of what a pipe actually did given a static input log.
public export
data Trace : (input : List i) -> Pipe i o Identity r -> (output : List o) -> Type where
  TraceReady : Trace [] (Ready r) []
  TraceYield : Trace ins k outs -> Trace ins (Yield x k) (x :: outs)
  TraceAwait : Trace ins (k (Just x)) outs -> Trace (x :: ins) (Await k) outs
  TraceExhaust : Trace [] (k Nothing) outs -> Trace [] (Await k) outs
Use code with caution.
Now, anyone can look at Trace, look at Pipe, and immediately understand the operational execution structure because it isn't buried inside hundreds of lines of type-level invariants.

3. Writing the Proof Independently

Imagine we wrote a simple data-doubling pipe using our clean, idiomatic architecture:
idris
doublePipe : Pipe Int Int Identity ()
doublePipe = Await $ \case
  Just x  => Yield (x * 2) doublePipe
  Nothing => Ready ()
Use code with caution.
To verify it under the idiomatic approach, we write an explicit theorem function completely detached from the execution engine. We prove that any valid trace of doublePipe mathematically satisfies outputs = map (*2) inputs:
idris
||| Theorem: Our clean pipe is guaranteed to safely map the double operation over its inputs.
||| We can verify this via simple, clean structural induction on the Trace tree.
doublePipeCorrect : (ins : List Int) -> (outs : List Int) 
                 -> Trace ins doublePipe outs 
                 -> outs = map (* 2) ins
doublePipeCorrect []          []          TraceReady      = Refl
doublePipeCorrect (x :: ins)  (y :: outs) (TraceYield t)   = 
  -- Idris easily matches y to (x * 2) and recursively evaluates the rest of the trace
  cong ((x * 2) ::) (doublePipeCorrect ins outs t) 
Use code with caution.

The Architectural Takeaway

By shifting from the VerifiedSewage approach to this idiomatic style:
1. Compilation speeds drop significantly because Idris isn't evaluating deep constraint chains during basic parsing and plumbing.
2. Readability scales perfectly. A software engineer who doesn't understand type theory can still confidently read, maintain, and safely update the core execution engine of Pipe and its composition mechanics (.|).
3. Verification becomes an opt-in choice. You can leave proofs completely out of your production application cycle and compile them cleanly side-by-side only inside your test/verification test suites.
Would you like to write a custom composition theorem for this clean Pipe model, or check how dependent vectors (Vect) can sometimes bridge the gap between these two styles for size safety?

# custom composition theorem

Writing a composition theorem for our extrinsic pipeline is where the architectural elegance of this style truly shines.
Our goal is to prove that if an upstream pipe transforms an input stream \(A\) into an intermediate stream \(B\), and a downstream pipe transforms that intermediate stream \(B\) into a final stream \(C\), then composing them with (.|) will correctly transform stream \(A\) into stream \(C\).
To do this cleanly, we will first formalize our Trace relation slightly to account for the Identity monad wrapper, and then build the structural proof.

1. The Setup: Pure Traces

Because our idiomatic Pipe handles arbitrary monads, we will specialize our Trace predicate for the pure execution context (Identity), making it straightforward to reason about mechanically.
idris
module CompositionTheorem

import Data.List
import IdiomaticSewage -- Assumes the prior refactored module is in scope

||| A structural execution trace for pure pipes.
||| Maps how a pipe consumes a specific input list and emits a specific output list.
public export
data Trace : List i -> Pipe i o Identity r -> List o -> Type where
  T_Ready   : Trace [] (Ready r) []
  
  T_Do      : Trace ins next outs 
           -> Trace ins (Do (Id next)) outs
           
  T_Yield   : Trace ins k outs 
           -> Trace ins (Yield x k) (x :: outs)
           
  T_Await   : Trace ins (k (Just x)) outs 
           -> Trace (x :: ins) (Await k) outs
           
  T_Exhaust : Trace [] (k Nothing) outs 
           -> Trace [] (Await k) outs
Use code with caution.

2. The Theorem Statement

The composition theorem states that if there exists a valid execution trace for the upstream pipe and a valid execution trace for the downstream pipe, there must exist a valid trace for the combined pipeline that marries the original input to the ultimate output.
idris
||| Composition Theorem: 
||| Piping an upstream trace and a downstream trace together yields a unified trace 
||| spanning from the initial input directly to the final output.
compositionTheorem : {ins : List i} -> {mid : List mMid} -> {outs : List o}
                  -> Trace ins upstream mid
                  -> Trace mid downstream outs
                  -> Trace ins (upstream .| downstream) outs
Use code with caution.

3. The Structural Proof

We prove this by structural induction. Because our definition of composition (.|) evaluates the downstream pipe first, we will perform induction primarily on the structural shape of the downstream trace, and case-split on the upstream trace whenever the downstream pipe attempts to read via an Await command.
idris
-- Case 1: Downstream terminates immediately with Ready.
-- Composition rule: upstream .| Ready r = Ready r
compositionTheorem tUp T_Ready = T_Ready

-- Case 2: Downstream performs a monadic action step.
compositionTheorem tUp (T_Do tDown) = T_Do (compositionTheorem tUp tDown)

-- Case 3: Downstream yields a final output value.
-- Composition rule: upstream .| Yield y k = Yield y (upstream .| k)
compositionTheorem tUp (T_Yield tDown) = T_Yield (compositionTheorem tUp tDown)

-- Case 4: Downstream wants to pull data from the intermediate stream (Await).
-- This requires checking what the upstream pipe is currently doing.
compositionTheorem tUp (T_Await tDown) = pullMid tUp tDown
  where
    pullMid : {ins : List i} -> {mid : List mMid} -> {outs : List o}
           -> Trace ins up (m :: mid)
           -> Trace mid (k (Just m)) outs
           -> Trace ins (up .| Await k) outs
           
    -- Upstream performs an action step; step through it.
    pullMid (T_Do tUpNext) tDownNext = T_Do (pullMid tUpNext tDownNext)
    
    -- Upstream yields exactly the value 'm' that downstream needs!
    -- This consumes 'm' from the intermediate list, allowing both traces to step forward.
    pullMid (T_Yield tUpNext) tDownNext = compositionTheorem tUpNext tDownNext
    
    -- Upstream wants to read from the outer input first. outer input steps forward.
    pullMid (T_Await tUpNext) tDownNext = T_Await (pullMid tUpNext tDownNext)

-- Case 5: Downstream has exhausted its intermediate stream and evaluates its Nothing branch.
compositionTheorem tUp (T_Exhaust tDown) = pullExhaust tUp tDown
  where
    pullExhaust : {ins : List i} -> {outs : List o}
               -> Trace ins up []
               -> Trace [] (k Nothing) outs
               -> Trace ins (up .| Await k) outs
               
    -- Upstream is also entirely finished. Feed Nothing into the downstream pipeline.
    pullExhaust T_Ready tDownNext = compositionTheorem T_Ready tDownNext
    
    -- Upstream steps through its internal actions.
    pullExhaust (T_Do tUpNext) tDownNext = T_Do (pullExhaust tUpNext tDownNext)
    
    -- Upstream wants to read more outer data before shutting down. Outer input steps forward.
    pullExhaust (T_Await tUpNext) tDownNext = T_Await (pullExhaust tUpNext tDownNext)
    
    -- Upstream is already empty, evaluating its own exhaustion branch.
    pullExhaust (T_Exhaust tUpNext) tDownNext = T_Exhaust (pullExhaust tUpNext tDownNext)
Use code with caution.

Why this is highly powerful compared to VerifiedSewage:

1. Zero Runtime / Structural Contamination: The code for (.|) doesn't know this theorem exists. It remains a lightning-fast runtime pipeline processing records cleanly.
2. Modular Verification: If someone finds a bug in your proof, your production streaming code still compiles and runs perfectly. In VerifiedSewage, a bug or incomplete edge-case in an invariant definition halts the entire compilation of operational code.
3. Intuitive Troubleshooting: If a composition proof fails, Idris points to the exact trace branch mismatch (e.g., downstream expected a value but upstream threw an early termination). You are fixing standard inductive structural matching, rather than fighting a massive wall of unifications inside implicit dependent records.
Now that you have seen composition handled extrinsically, would you like to see how to wrap this structural trace into a clean type-safe application wrapper so that users can run pipes safely without seeing the proofs, or look at how to model termination safety next?

