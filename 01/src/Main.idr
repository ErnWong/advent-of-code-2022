module Main

import Control.App
import Control.App.Console

hello : Console es => App es()
hello = getLine >>= \x => putStrLn x >>= \y => putStrLn x

main : IO ()
main = run hello
