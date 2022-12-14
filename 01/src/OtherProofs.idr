||| This module contains other proofs for VerifiedSewage that needs to be
||| defined outside the VerifiedSewage module so that we can make sure these
||| proofs only rely on the type signatures and not the function body definitions
||| of the things they are trying to prove. In particular, if we defined these
||| proofs inside VerifiedSewage, Idris would try to evaluate/reduce the expressions
||| at compile time to their weak head normal forms using the function body definitions
||| and end up using a lot of memory (> 8GB) and time (> 30 minutes - I don't know it
||| might have hanged indefinitely so I force-quitted it).
module OtherProofs

import Control.Monad.Identity
import Data.DPair
import Data.Nat

import Basics
import VerifiedSewage


covering
0 forAllPossibleInputs_sumPipeIsEquivalentToFoldrSum :
    (input : List Nat)
    -> fst (
        runInputExhaustingPurePipeWithList
            {returnInvariant = VerifiedSewage.sum_returnInvariant}
            VerifiedSewage.sum
            input
    ) = foldr (+) 0 (reverse input)
forAllPossibleInputs_sumPipeIsEquivalentToFoldrSum input
    = snd $ runInputExhaustingPurePipeWithList sum input


covering
0 forAllPossibleInputs_maxPipeIsEquivalentToFoldrMax :
    (input : List Nat)
    -> fst (
        runInputExhaustingPurePipeWithList
            {returnInvariant = VerifiedSewage.max_returnInvariant}
            VerifiedSewage.max
            input
    ) = foldr Data.Nat.maximum 0 (reverse input)
forAllPossibleInputs_maxPipeIsEquivalentToFoldrMax input
    = snd $ runInputExhaustingPurePipeWithList max input