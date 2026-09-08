module Mip where

open import Formulae 
open import SeqCalc

record MIP (A C : Fma) : Set where
  constructor intrp
  field
    D : Fma
    -- g : D ⊢ C
    -- h : A ⊢ D
    g : A ⊢ D
    h : D ⊢ C

mip : {A C : Fma} → (f : A ⊢ C)
  → MIP A C
mip ax = intrp _ ax ax
mip ⊤r = intrp ⊤ ⊤r ax
mip ⊥l = intrp ⊥ ax ⊥l
mip (∧r f f') = 
  let intrp D g h = mip f
      intrp D' g' h' = mip f'
  in intrp _ (∧r g g') (∧r (∧l₁ h) (∧l₂ h'))
mip (∧l₁ f) =
  let intrp D g h = mip f
  in intrp D (∧l₁ g) h
mip (∧l₂ f) =
  let intrp D g h = mip f
  in intrp D (∧l₂ g) h
mip (∨r₁ f) =
  let intrp D g h = mip f
  in intrp D g (∨r₁ h)
mip (∨r₂ f) =
  let intrp D g h = mip f
  in intrp D g (∨r₂ h)
mip (∨l f f') =
  let intrp D g h = mip f
      intrp D' g' h' = mip f'
  in intrp _ (∨l (∨r₁ g) (∨r₂ g')) (∨l h h')
