{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoFieldSelectors #-}
module Main (main) where

import Synthesis
import IR
import Options.Applicative
import qualified Prettyprinter as P
import Util

data Arguments = Arguments
  { inputFile :: String
  , outputCore :: Bool
  , outputIr :: Bool
  , outputFiltered :: Bool
  , process :: String
  }

parseArguments :: Parser Arguments
parseArguments =
  Arguments
    <$> strArgument (metavar "input")
    <*> (flag False True (long "output-core") <|> flag' False (long "no-output-core"))
    <*> (flag False True (long "output-ir") <|> flag' False (long "no-output-ir"))
    <*> (flag True True (long "output-filtered") <|> flag' False (long "no-output-filtered"))
    <*> option (str >>= \s -> pure s) (long "process" <> value "system")

argumentParser :: ParserInfo Arguments
argumentParser =
  info
    (parseArguments <**> helper)
    (fullDesc)

main :: IO ()
main = do
  arguments <- execParser argumentParser
  (core, dflags) <- compileToCore Nothing (arguments.inputFile)
  let ir = translate core
  let filtered = filterUnused arguments.process ir
  if arguments.outputCore then putStrLn $ showPpr dflags core else pure ()
  if arguments.outputIr then print ir else pure ()
  case filtered of
    Just p@(m, r) -> do
      if arguments.outputFiltered then (print . P.pretty) p else pure ()
      print . P.pretty $ synthesize r m ([] :: [Context Process Id], [])
    Nothing -> error $ "No such process: " <> arguments.process
  pure ()
