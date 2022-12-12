module Main

import Control.App.Console
import Control.App.FileIO

import VerifiedSewage


-- Halting problem go brrr...
%default total


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
