
module Main where

-- Some basic facts about lists
import Utilities

-- Formulae
import Formulae

-- Sequent Calculus
import SeqCalc

-- Focused calculus
import FocusedSeqCalc

import Focus
import Emb

{-
Equivalent derivations in sequent calculus 
are identical in focused calculus.
-}
import FocusWellDef

{-
Every derivation in sequent calculus is 
≗-related to its normal form.
i.e. emb-ri (focus f) ≗ f.
-}
import EmbFocus

{-
Focused derivations are in normal form,
i.e. focus (emb-ri f) ≡ f.
-}
import FocusEmb
