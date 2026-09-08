module Cut where

open import Formulae 
open import SeqCalc

cut : {A B C : Fma} 
  → (f : A ⊢ B) (g : B ⊢ C)
  → A ⊢ C
cut f ax = f
cut f ⊤r = ⊤r
cut ax ⊥l = ⊥l
cut ⊥l ⊥l = ⊥l
cut (∧l₁ f) ⊥l = ∧l₁ (cut f ⊥l)
cut (∧l₂ f) ⊥l = ∧l₂ (cut f ⊥l)
cut (∨l f f₁) ⊥l = ∨l (cut f ⊥l) (cut f₁ ⊥l)
cut f (∧r g g₁) = ∧r (cut f g) (cut f g₁)
cut ax (∧l₁ g) = ∧l₁ g
cut ⊥l (∧l₁ g) = ⊥l
cut (∧r f f₁) (∧l₁ g) = cut f g
cut (∧l₁ f) (∧l₁ g) = ∧l₁ (cut f (∧l₁ g))
cut (∧l₂ f) (∧l₁ g) = ∧l₂ (cut f (∧l₁ g))
cut (∨l f f₁) (∧l₁ g) = ∨l (cut f (∧l₁ g)) (cut f₁ (∧l₁ g))
cut ax (∧l₂ g) = ∧l₂ g
cut ⊥l (∧l₂ g) = ⊥l
cut (∧r f f₁) (∧l₂ g) = cut f₁ g
cut (∧l₁ f) (∧l₂ g) = ∧l₁ (cut f (∧l₂ g))
cut (∧l₂ f) (∧l₂ g) = ∧l₂ (cut f (∧l₂ g))
cut (∨l f f₁) (∧l₂ g) = ∨l (cut f (∧l₂ g)) (cut f₁ (∧l₂ g))
cut f (∨r₁ g) = ∨r₁ (cut f g)
cut f (∨r₂ g) = ∨r₂ (cut f g)
cut ax (∨l g g₁) = ∨l g g₁
cut ⊥l (∨l g g₁) = ⊥l
cut (∧l₁ f) (∨l g g₁) = ∧l₁ (cut f (∨l g g₁))
cut (∧l₂ f) (∨l g g₁) = ∧l₂ (cut f (∨l g g₁))
cut (∨r₁ f) (∨l g g₁) = cut f g
cut (∨r₂ f) (∨l g g₁) = cut f g₁
cut (∨l f f₁) (∨l g g₁) = ∨l (cut f (∨l g g₁)) (cut f₁ (∨l g g₁))