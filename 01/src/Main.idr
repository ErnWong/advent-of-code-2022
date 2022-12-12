module Main

import Control.App.Console
import Control.App.FileIO
import Control.Monad.Identity
import Data.DPair
import Data.Nat

import VerifiedSewage


-- Halting problem go brrr...
%default total


covering
forAllPossibleInputs_maxPipeIsEquivalentToFoldrMax :
    (input: List Nat)
    -> ErasedThing (
        fst (
            runInputExhaustingPurePipeWithList
                {returnInvariant = VerifiedSewage.maxReturnInvariant}
                VerifiedSewage.max
                input
        ) = foldr Data.Nat.maximum 0 (reverse input)
    )
forAllPossibleInputs_maxPipeIsEquivalentToFoldrMax input
    = MkErasedThing $ snd $ runInputExhaustingPurePipeWithList max input


covering
app : Has [FileIO, Console] effects => Control.App.App effects ()
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
