module Main

import Control.App
import Control.App.Console

%default total

hello : Console es => App es()
hello = getLine >>= \x => putStrLn x >>= \y => putStrLn x

partial
main : IO ()
main = run hello
