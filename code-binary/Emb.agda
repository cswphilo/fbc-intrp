module Emb where

open import Data.List
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])

open import Utilities
open import Formulae
open import SeqCalc
open import FocusedSeqCalc

emb-ri : ∀ {S C} (f : S ⊢ri C) → S ⊢ C
emb-li : ∀ {S C} (f : S ⊢li C) → S ⊢ pos C
emb-f : ∀ {S C} (f : S ⊢f C) → neg S ⊢ pos C

emb-ri (∧r f f₁) = ∧r (emb-ri f) (emb-ri f₁)
emb-ri (li2ri f) = emb-li f

emb-li (∨l f g) = ∨l (emb-li f) (emb-li g)
emb-li (f2li f) = emb-f f

emb-f ax = ax
emb-f (∧l₁ f) = ∧l₁ (emb-li f)
emb-f (∧l₂ f) = ∧l₂ (emb-li f)
emb-f (∨r₁ f ok) = ∨r₁ (emb-ri f)
emb-f (∨r₂ f ok) = ∨r₂ (emb-ri f)


