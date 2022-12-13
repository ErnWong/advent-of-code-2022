module Basics

import Data.List
import Data.List.Reverse


||| A dummy data type for easily returning a proof object that is guaranteed
||| to be erased at runtime. Maybe there's already an existing Idris builtin for
||| this, but I haven't found it yet.
public export
data ErasedThing : (0 a : Type) -> Type where
    MkErasedThing : (0 thing : a) -> ErasedThing a


||| Similar to `ErasedThing` but for dependent pairs, where both the `fst` and
||| `snd` are erased at runtime. This is similar to `DPair`, `Subset`, and `Exists`,
||| but whereas those are (1) not erased, (2) only `snd` erased, and (3) onky `fst`
||| erased respectively, for some reason there isn't one to erase both (or maybe
||| there is but I just haven't found it yet).
public export
record ErasedDPair {0 a : Type} {0 b : a -> Type} where
    constructor MkErasedDPair
    0 fst : a
    0 snd : b fst


export
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


export
reverseMovesHeadToEnd : (x : a) -> (xs : List a) -> reverse (x :: xs) = (reverse xs) ++ [x]
reverseMovesHeadToEnd x xs = reverseOntoSpec [x] xs
