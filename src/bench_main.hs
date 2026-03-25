module Main where

import System.Environment (getArgs)
import System.Exit (die)

import Bench

main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
    Right cfg -> runBench cfg
    Left msg -> die msg
