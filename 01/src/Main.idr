module Main

import Control.App.Console
import Control.App.FileIO
import Data.Vect
import System.File

import Basics
import VerifiedSewage


-- Halting problem go brrr...
%default total


covering
part1 : Has [FileIO, Console] effects => Control.App.App effects ()
part1 = runPipe $
    readLines
    .| splitByEmptyLine (parseNat .| sum)
    .| max
    .| printReturnValue


covering
part2 : Has [FileIO, Console] effects => Control.App.App effects ()
part2 = do
    topThree <- runPipe $
        readLines
        .| splitByEmptyLine (parseNat .| sum)
        .| maxN 3
    let topThreeSum = foldr (+) 0 topThree
    putStrLn $ show topThreeSum


covering
app : Has [FileIO, Console, System] effects => Control.App.App effects ()
app = do
    args <- getArgs
    case args of
        [_, "1"] => part1
        [_, "2"] => part2
        (_ :: options) => do
            fPutStrLn stderr "Unknown part number \{show options}"
            exitFailure
        [] => do
            fPutStrLn stderr "Unknown part number (no arguments found)"
            exitFailure


covering
main : IO ()
main = run $ handle app
    (\() => pure ())
    (\error : IOError => do
        putStrLn "An error has occured: \{show error}"
        exitFailure
    )
