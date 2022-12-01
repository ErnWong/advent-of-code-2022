module Main

import Control.App
import Control.App.Console
import Control.App.FileIO
import Data.Colist
import System.File.Virtual

%default total

partial
readLines : Has [FileIO, Console] effects => App effects (Colist String)
readLines = do
    putStrLn "Reading next line..."
    -- TODO: Does this skip the last line?
    line <- getLine
    eof <- fEOF stdin
    if eof
        then pure []
        else do
            rest <- readLines
            pure (line :: rest)

partial
printLines : Has [Console] effects => Colist String -> App effects ()
printLines [] = putStrLn "Done"
printLines (line :: rest) = do
    putStrLn $ "Line: " ++ line
    printLines rest

partial
main : IO ()
main = run $ handle (readLines >>= printLines)
    (\() => putStr "Ok")
    (\error : IOError => putStr "Error")
