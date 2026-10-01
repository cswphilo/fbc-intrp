module VarCondition where

import Data.Empty as Empty
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
open import Formulae

infix 4 _∈F_

_∈F_ : At → Fma → Set
X ∈F (` Y) = X ≡ Y
X ∈F ⊤ = Empty.⊥
X ∈F ⊥ = Empty.⊥
X ∈F (A ∧ B) = X ∈F A ⊎ X ∈F B
X ∈F (A ∨ B) = X ∈F A ⊎ X ∈F B
