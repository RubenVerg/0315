{-# LANGUAGE TemplateHaskell #-}

module Lang0315.Sequences
( sequences
) where

import Numeric.Natural
import Lang0315.Sequence
import Lang0315.Sequences.TH
import Lang0315.Sequences.Implementation

sequences :: [(Natural, (Sequence, Maybe String))]
sequences = $(sequencesExpr)
