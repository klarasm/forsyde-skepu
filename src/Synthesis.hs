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
import qualified Data.Set as S
import Prettyprinter

data (Show a, Show b) => Context a b = Context
  { from :: b
  , ret :: Type
  , inputs :: [(Type, String)]
  , outputs :: [(Type, String)]
  , delayStorage :: S.Set (Type, String, Expression)
  , body :: Statement
  }
  deriving (Show)
instance (Show a, Show b, Pretty a, Pretty b) => Pretty (Context a b) where
  pretty Context { .. } =
    pretty "Context"
      <> (nest 4 . tupled)
        [ pretty from
        , pretty ret
        , pretty inputs
        , pretty outputs
        , pretty . S.elems $ delayStorage
        , pretty body
        ]

class Synthesizable a b where
  -- may need to resolve a previously unresolved process as dependency
  synthesize :: [a] -> a -> ([Context a b], [Context a b]) -> ([Context a b], [Context a b])
