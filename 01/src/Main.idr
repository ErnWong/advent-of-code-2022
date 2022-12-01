module Main

import Control.App
import Control.App.Console

%default total

partial
hello : Console es => App es()
hello = do putStr "Enter text: "
           text <- getLine
           putStrLn $ "Text is " ++ text
           hello

partial
main : IO ()
main = run hello
