
module Formulae where

-- import Data.Unit as Unit
-- import Data.Empty as Empty

-- open import Utilities

postulate At : Set

-- Formulae
data Fma : Set where 
  ` : At → Fma
  ⊤ : Fma
  ⊥ : Fma
  _∧_ : Fma → Fma → Fma
  _∨_ : Fma → Fma → Fma

infix 22 _∧_ _∨_

{-
-- Predicates on formulae checking whether

-- the formula is negative
isNeg : Fma → Set
isNeg (` x) = Unit.⊤
isNeg (x ∧ x₁) = Unit.⊤
isNeg (x ∨ x₁) = Empty.⊥

record Neg : Set where
  constructor mkNeg
  field
    A : Fma
    .isneg : isNeg A

neg : Neg → Fma
neg (mkNeg S s) = S

-- the formula is positive
isPos : Fma → Set
isPos (` x) = Unit.⊤
isPos (x ∧ x₁) = Empty.⊥
isPos (x ∨ x₁) = Unit.⊤


record Pos : Set where
  constructor mkPos
  field
    A : Fma
    .ispos : isPos A

pos : Pos → Fma
pos (mkPos A a) = A


 
toTree : Fma → Tree Pos
toTree (` X) = leaf (mkPos (` X) _)
toTree (A ∧ B) = node (toTree A) (toTree B)
toTree (A ∨ B) = leaf (mkPos (A ∨ B) _)
-}
