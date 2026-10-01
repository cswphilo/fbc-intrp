module Mip where

open import Data.Sum using (inj₁; inj₂) renaming ([_,_]′ to elim⊎)
open import Formulae 
open import SeqCalc
open import VarCondition

record MIP (A C : Fma) : Set where
  constructor intrp
  field
    D : Fma
    g : A ⊢ D
    h : D ⊢ C
    varg : ∀ {X} → X ∈F D → X ∈F A
    varh : ∀ {X} → X ∈F D → X ∈F C

mip : {A C : Fma} → (f : A ⊢ C)
  → MIP A C
mip ax = intrp _ ax ax (λ m → m) (λ m → m)
mip ⊤r = intrp ⊤ ⊤r ax (λ ()) (λ ())
mip ⊥l = intrp ⊥ ax ⊥l (λ ()) (λ ())
mip (∧r f f') = 
  let intrp D g h vg vh = mip f
      intrp D' g' h' vg' vh' = mip f'
  in intrp _ (∧r g g') (∧r (∧l₁ h) (∧l₂ h'))
       (λ m → elim⊎ vg vg' m)
       (λ m → elim⊎ (λ p → inj₁ (vh p)) (λ p → inj₂ (vh' p)) m)
mip (∧l₁ f) =
  let intrp D g h vg vh = mip f
  in intrp D (∧l₁ g) h (λ m → inj₁ (vg m)) vh
mip (∧l₂ f) =
  let intrp D g h vg vh = mip f
  in intrp D (∧l₂ g) h (λ m → inj₂ (vg m)) vh
mip (∨r₁ f) =
  let intrp D g h vg vh = mip f
  in intrp D g (∨r₁ h) vg (λ m → inj₁ (vh m))
mip (∨r₂ f) =
  let intrp D g h vg vh = mip f
  in intrp D g (∨r₂ h) vg (λ m → inj₂ (vh m))
mip (∨l f f') =
  let intrp D g h vg vh = mip f
      intrp D' g' h' vg' vh' = mip f'
  in intrp _ (∨l (∨r₁ g) (∨r₂ g')) (∨l h h')
       (λ m → elim⊎ (λ p → inj₁ (vg p)) (λ p → inj₂ (vg' p)) m)
       (λ m → elim⊎ vh vh' m)
