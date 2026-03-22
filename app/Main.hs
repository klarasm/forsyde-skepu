module Main (main) where

import Options.Applicative
-- import GHC.Core
import Util
import IR

data Arguments = Arguments
  { inputFile :: String
  , outputCore :: Bool
  , outputIr :: Bool
  }

parseArguments :: Parser Arguments
parseArguments =
  Arguments
    <$> strArgument (metavar "input")
    <*> flag False True (long "output-core")
    <*> flag True False (long "no-output-ir")

argumentParser :: ParserInfo Arguments
argumentParser =
  info
    (parseArguments <**> helper)
    (fullDesc)

main :: IO ()
main = do
  arguments <- execParser argumentParser
  (core, dflags) <- compileToCore Nothing (inputFile arguments)
  if outputCore arguments
    then putStrLn $ showPpr dflags core
    else pure ()
  let ir = translate core
  if outputIr arguments
    then print ir
    else pure ()
  pure ()
