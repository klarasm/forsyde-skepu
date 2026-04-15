{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Synthesis (
  Context (..),
  Synthesizable (..),
) where

import CIR
import Prettyprinter

data (Show a, Show b) => Context a b = Context
  { from :: b
  , ret :: Type
  , name :: String
  , params :: [(Type, String)]
  , delayStorage :: [(Type, String, Expression)]
  , body :: Statement
  }
  deriving (Show)
instance (Show a, Show b, Pretty a, Pretty b) => Pretty (Context a b) where
  pretty Context { .. } =
    pretty "Context"
      <> (nest 4 . tupled)
        [ pretty from
        , pretty ret
        , pretty name
        , pretty params
        , pretty delayStorage
        , pretty body
        ]

class Synthesizable a b where
  -- may need to resolve a previously unresolved process as dependency
  synthesize :: [a] -> a -> ([Context a b], [Context a b]) -> ([Context a b], [Context a b])
