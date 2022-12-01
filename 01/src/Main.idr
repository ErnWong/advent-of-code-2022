module Main

import Control.App
import Control.App.Console

hello : Console es => App es()
hello = getLine >>= putStrLn >>= \x => putStrLn "end"

main : IO ()
main = run hello
