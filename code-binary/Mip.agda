module Mip where

open import Formulae 
open import SeqCalc

record MIP (A C : Fma) : Set where
  constructor intrp
  field
    D : Fma
    g : D ⊢ C
    h : A ⊢ D

mip : {A C : Fma} → (f : A ⊢ C)
  → MIP A C
mip ax = intrp _ ax ax
mip (∧r f f') = 
  let intrp D g h = mip f
      intrp D' g' h' = mip f'
  in intrp _ (∧r (∧l₁ g) (∧l₂ g')) (∧r h h')
mip (∧l₁ f) =
  let intrp D g h = mip f
  in intrp D g (∧l₁ h)
mip (∧l₂ f) =
  let intrp D g h = mip f
  in intrp D g (∧l₂ h)
mip (∨r₁ f) =
  let intrp D g h = mip f
  in intrp D (∨r₁ g) h
mip (∨r₂ f) =
  let intrp D g h = mip f
  in intrp D (∨r₂ g) h
mip (∨l f f') =
  let intrp D g h = mip f
      intrp D' g' h' = mip f'
  in intrp _ (∨l g g') (∨l (∨r₁ h) (∨r₂ h'))
