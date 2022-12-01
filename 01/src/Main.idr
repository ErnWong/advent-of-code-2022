module Main

import Control.App
import Control.App.Console
import Control.App.FileIO
import System.File.Virtual

%default total

partial
hello : Has [FileIO, Console] es => App es()
hello = do
           eof <- fEOF stdin
           if eof
             then pure ()
             else do putStr "Enter text: "
                     text <- getLine
                     putStrLn $ "Text is " ++ text
                     hello

partial
main : IO ()
main = run $ handle hello (\() => putStr "Ok") (\err : IOError => putStr "Error")
