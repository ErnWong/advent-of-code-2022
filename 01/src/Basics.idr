module Basics

import Data.List
import Data.List.Elem
import Data.List.Reverse
import Data.List1
import Data.Nat


||| A dependent pair, but where both the `fst` and `snd` are erased at runtime.
||| This is similar to `DPair`, `Subset`, and `Exists`, but whereas those are
||| (1) not erased, (2) only `snd` erased, and (3) only `fst` erased respectively,
||| for some reason there isn't one to erase both (or maybe there is but I just
||| haven't found it yet).
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


||| Copied over from Idris2 v0.6.0 /libs/base/Data/Nat.idr
export
maximumLeftUpperBound : (m, n : Nat) -> m `LTE` maximum m n
maximumLeftUpperBound 0 n = LTEZero
maximumLeftUpperBound (S m) 0 = reflexive
maximumLeftUpperBound (S m) (S n) = LTESucc (maximumLeftUpperBound m n)


||| Copied over from Idris2 v0.6.0 /libs/base/Data/Nat.idr
export
maximumRightUpperBound : (m, n : Nat) -> n `LTE` maximum m n
maximumRightUpperBound 0 n = reflexive
maximumRightUpperBound (S m) 0 = LTEZero
maximumRightUpperBound (S m) (S n) = LTESucc (maximumRightUpperBound m n)


foldrMaxIsDistributive :
    (xs : List Nat)
    -> (ys : List Nat)
    -> ((foldr Data.Nat.maximum 0 (xs ++ ys)) = (Data.Nat.maximum (foldr Data.Nat.maximum 0 xs) $ foldr Data.Nat.maximum 0 ys))
foldrMaxIsDistributive [] ys = Refl
foldrMaxIsDistributive (x :: xs) ys =
    let
        original :
            (Data.Nat.maximum (foldr Data.Nat.maximum 0 (x :: xs)) (foldr Data.Nat.maximum 0 ys)
            = Data.Nat.maximum (foldr Data.Nat.maximum 0 (x :: xs)) (foldr Data.Nat.maximum 0 ys))
        original = Refl

        moveXOutOfFold :
            (Data.Nat.maximum (Data.Nat.maximum x (foldr Data.Nat.maximum 0 xs)) (foldr Data.Nat.maximum 0 ys)
            = Data.Nat.maximum (foldr Data.Nat.maximum 0 (x :: xs)) (foldr Data.Nat.maximum 0 ys))
        moveXOutOfFold = original

        moveXToOuterMax :
            (Data.Nat.maximum x (Data.Nat.maximum (foldr Data.Nat.maximum 0 xs) (foldr Data.Nat.maximum 0 ys))
            = Data.Nat.maximum (foldr Data.Nat.maximum 0 (x :: xs)) (foldr Data.Nat.maximum 0 ys))
        moveXToOuterMax =
            rewrite
                maximumAssociative x (foldr maximum 0 xs) (foldr maximum 0 ys)
            in
                moveXOutOfFold

        substituteInRecursion :
            (Data.Nat.maximum x (foldr Data.Nat.maximum 0 (xs ++ ys))
            = Data.Nat.maximum (foldr Data.Nat.maximum 0 (x :: xs)) (foldr Data.Nat.maximum 0 ys))
        substituteInRecursion =
            rewrite
                foldrMaxIsDistributive xs ys
            in
                moveXToOuterMax

        moveXBackIn :
            (foldr Data.Nat.maximum 0 (x :: (xs ++ ys))
            = Data.Nat.maximum (foldr Data.Nat.maximum 0 (x :: xs)) (foldr Data.Nat.maximum 0 ys))
        moveXBackIn = substituteInRecursion
    in
        moveXBackIn


maxOfEmptyListIsZero : 0 = (foldr Data.Nat.maximum 0 [])
maxOfEmptyListIsZero = Refl


maxOfSingleNatIsItself :
    (x : Nat)
    -> (x = (foldr Data.Nat.maximum 0 [x]))
maxOfSingleNatIsItself x =
    rewrite sym maxOfEmptyListIsZero in
        rewrite maximumCommutative x 0 in
            Refl


export
foldrMaxSameWhenReversed :
    (input : List Nat)
    -> foldr Data.Nat.maximum 0 input = foldr Data.Nat.maximum 0 (reverse input)
foldrMaxSameWhenReversed [] = Refl
foldrMaxSameWhenReversed (x :: xs) =
    let
        moveXOut :
            ((foldr Data.Nat.maximum 0 (x :: xs))
            = (Data.Nat.maximum x $ foldr Data.Nat.maximum 0 xs))
        moveXOut = Refl

        swapAround :
            ((foldr Data.Nat.maximum 0 (x :: xs))
            = (Data.Nat.maximum (foldr Data.Nat.maximum 0 xs) x))
        swapAround =
            rewrite
                maximumCommutative (foldr maximum 0 xs) x
            in
                moveXOut

        substituteInRecursion :
            ((foldr Data.Nat.maximum 0 (x :: xs))
            = (Data.Nat.maximum (foldr Data.Nat.maximum 0 (reverse xs)) x))
        substituteInRecursion =
            rewrite
                sym $ foldrMaxSameWhenReversed xs
            in
                swapAround

        wrapXInDegenerateMax :
            ((foldr Data.Nat.maximum 0 (x :: xs))
            = (Data.Nat.maximum (foldr Data.Nat.maximum 0 (reverse xs)) (foldr Data.Nat.maximum 0 [x])))
        wrapXInDegenerateMax =
            rewrite
                sym $ maxOfSingleNatIsItself x
            in
                substituteInRecursion

        moveXIntoFold :
            ((foldr Data.Nat.maximum 0 (x :: xs))
            = (foldr Data.Nat.maximum 0 ((reverse xs) ++ [x])))
        moveXIntoFold =
                wrapXInDegenerateMax
                `trans`
                (sym $ foldrMaxIsDistributive (reverse xs) [x])

        moveXIntoReverse :
            ((foldr Data.Nat.maximum 0 (x :: xs))
            = (foldr Data.Nat.maximum 0 (reverse (x :: xs))))
        moveXIntoReverse =
            rewrite
                reverseOntoSpec [x] xs
            in
                moveXIntoFold
    in
        moveXIntoReverse


ifLessThanOrEqThenNotMax :
    (x, y : Nat)
    -> x `LTE` y
    -> maximum x y = y
ifLessThanOrEqThenNotMax 0 y LTEZero = Refl
ifLessThanOrEqThenNotMax (S x) (S y) (LTESucc succ) =
    -- We need to use replace instead of rewrite here because
    -- we only want to substitute into the RHS and not the LHS.
    replace
        {p = \y1 => maximum (S x) (S y) = S y1}
        (ifLessThanOrEqThenNotMax x y succ)
        (sym $ maximumSuccSucc x y)


ifGreaterThanThenMax :
    (x, y : Nat)
    -> (x `GT` y)
    -> maximum x y = x
ifGreaterThanThenMax (S x) 0 (LTESucc _) = Refl
ifGreaterThanThenMax (S x) (S y) (LTESucc succ) =
    -- We need to use replace instead of rewrite here because
    -- we only want to substitute into the RHS and not the LHS.
    replace
        {p = \x1 => maximum (S x) (S y) = S x1}
        (ifGreaterThanThenMax x y succ)
        (sym $ maximumSuccSucc x y)


export
foldrMaxIsElementOfNonemptyList :
    (list : List1 Nat)
    -> Elem (foldr Data.Nat.maximum 0 (forget list)) $ forget list
foldrMaxIsElementOfNonemptyList (x ::: []) =
    let
        xIsElement : Elem x [x]
        xIsElement = Here

        maxWithZeroIsItself : (y : Nat) -> Data.Nat.maximum y 0 = y
        maxWithZeroIsItself Z = Refl
        maxWithZeroIsItself (S n) = Refl
    in
        rewrite maxWithZeroIsItself x in xIsElement
foldrMaxIsElementOfNonemptyList (x ::: (y :: xs)) =
    let
        remainingMax : Nat
        remainingMax = foldr maximum 0 (y :: xs)
    in
        case x `isLTE` remainingMax of
            Yes xLessThanOrEq =>
                rewrite
                    ifLessThanOrEqThenNotMax x remainingMax xLessThanOrEq
                in
                    There $ foldrMaxIsElementOfNonemptyList (y ::: xs)
            No xNotLessThanOrEq =>
                rewrite
                    ifGreaterThanThenMax x remainingMax (notLTEImpliesGT xNotLessThanOrEq)
                in
                    Here


foldrMaxMonotonicallyIncreases :
    (xs : List Nat)
    -> (x : Nat)
    -> (foldr Data.Nat.maximum 0 xs `LTE` foldr Data.Nat.maximum 0 (x :: xs))
foldrMaxMonotonicallyIncreases xs x = maximumRightUpperBound x (foldr maximum 0 xs)


export
foldrMaxIsUpperBound :
    (list : List Nat)
    -> (element : Nat)
    -> (elementIsInList : Elem element list)
    -> (element `LTE` foldr Data.Nat.maximum 0 list)
foldrMaxIsUpperBound (x :: xs) x Here = maximumLeftUpperBound x (foldr Data.Nat.maximum 0 xs)
foldrMaxIsUpperBound (y :: xs) x (There there)
    = foldrMaxIsUpperBound xs x there `transitive` foldrMaxMonotonicallyIncreases xs y
