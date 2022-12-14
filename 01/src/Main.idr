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
    .| splitByEmptyLine (parseNat .| sum)
    .| max
    .| printReturnValue


covering
main : IO ()
main = run $ handle app
    (\() => pure ())
    (\error : IOError => putStr "An error has occured: \{show error}")
