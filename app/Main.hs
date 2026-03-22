module Main (main) where

import Options.Applicative
import GHC.Core
import Util
import IR

data Arguments = Arguments {
  inputFile :: String
}

parseArguments :: Parser Arguments
parseArguments =
  Arguments
    <$> strArgument (metavar "input")

argumentParser :: ParserInfo Arguments
argumentParser =
  info
    (parseArguments <**> helper)
    (fullDesc)

main :: IO ()
main = do
  arguments <- execParser argumentParser
  (core, dflags) <- compileToCore Nothing (inputFile arguments)
  print $ translate core
  -- putStrLn $ showPpr dflags core
  -- _ <- traverse (putStrLn . showPpr dflags . f) core
  -- _ <- traverse (putStrLn . showPpr dflags) core
  pure ()
  where
    f (NonRec _ e) = e
    f (Rec _) = undefined
    g (binds, body) = stripNArgs (fromIntegral $ length binds) body
