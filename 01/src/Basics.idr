module Basics

import Data.List
import Data.List.Reverse


public export
data ErasedThing : (0 a : Type) -> Type where
    MkErasedThing : (0 thing : a) -> ErasedThing a


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