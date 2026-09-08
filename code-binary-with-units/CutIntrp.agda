module CutIntrp where

open import Formulae 
open import SeqCalc
open import Cut
open import CutProperties
open import Mip

cut-intrp : ∀ {A C : Fma} 
  → (f : A ⊢ C)
  → cut (MIP.g (mip f)) (MIP.h (mip f)) ≗ f
cut-intrp ax = refl
cut-intrp ⊤r = refl
cut-intrp ⊥l = refl
cut-intrp (∧r f f₁) = ∧r (cut-intrp f) (cut-intrp f₁)
cut-intrp (∧l₁ f) = cut∧l₁≗ (mip f .MIP.g) (mip f .MIP.h) ∙ ∧l₁ (cut-intrp f)
cut-intrp (∧l₂ f) = cut∧l₂≗ (mip f .MIP.g) (mip f .MIP.h) ∙ ∧l₂ (cut-intrp f)
cut-intrp (∨r₁ f) = ∨r₁ (cut-intrp f)
cut-intrp (∨r₂ f) = ∨r₂ (cut-intrp f)
cut-intrp (∨l f f₁) = ∨l (cut-intrp f) (cut-intrp f₁)
