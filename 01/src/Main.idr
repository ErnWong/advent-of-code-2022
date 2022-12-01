module Main

import Control.App
import Control.App.Console

hello : Console es => App es()
hello = getLine >>= putStrLn

main : IO ()
main = run hello
