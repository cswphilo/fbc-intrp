module IntrpTriples where

open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open import Formulae
open import SeqCalc
open import Cut
open import Mip
open import VarCondition

_⊩_ : ∀ {A C} → (n n' : MIP A C) → Set
_⊩_ (intrp D₁ g₁ h₁ vg₁ vh₁) (intrp D₂ g₂ h₂ vg₂ vh₂) =
  Σ (D₁ ⊢ D₂) λ t → (cut g₁ t ≗ g₂) × (h₁ ≗ cut t h₂)

data _~_ {A C : Fma} : MIP A C → MIP A C → Set where
  refl : {n : MIP A C} → n ~ n
  ↝∷ : {n n' p : MIP A C}
          → n ⊩ n' → n' ~ p
          → n ~ p
  ↜∷ : {n n' p : MIP A C}
          → n' ⊩ n → n' ~ p
          → n ~ p

∷↝ : {A C : Fma}
  → {n n' p : MIP A C}
  → n ⊩ n' → p ~ n'
  → p ~ n
∷↝ x refl = ↜∷ x refl
∷↝ x (↝∷ y eq) = ↝∷ y (∷↝ x eq)
∷↝ x (↜∷ y eq) = ↜∷ y (∷↝ x eq)

∷↜ : {A C : Fma}
  → {n n' p : MIP A C}
  → n' ⊩ n → p ~ n'
  → p ~ n
∷↜ x refl = ↝∷ x refl
∷↜ x (↝∷ y eq) = ↝∷ y (∷↜ x eq)
∷↜ x (↜∷ y eq) = ↜∷ y (∷↜ x eq)

~-sym : {A C : Fma}
  → {n n' : MIP A C}
  → n ~ n'
  → n' ~ n
~-sym refl = refl
~-sym (↝∷ x eq) = ∷↝ x (~-sym eq)
~-sym (↜∷ x eq) = ∷↜ x (~-sym eq)

~-trans : {A C : Fma}
  → {n n' n'' : MIP A C}
  → n ~ n' → n' ~ n''
  → n ~ n''
~-trans refl eq₂ = eq₂
~-trans (↝∷ x eq₁) eq₂ = ↝∷ x (~-trans eq₁ eq₂)
~-trans (↜∷ x eq₁) eq₂ = ↜∷ x (~-trans eq₁ eq₂)

cutaxA-left' : ∀ {A C} (f : A ⊢ C) → cut ax f ≡ f
cutaxA-left' ax = refl
cutaxA-left' ⊤r = refl
cutaxA-left' ⊥l = refl
cutaxA-left' (∧r f f₁) = cong₂ ∧r (cutaxA-left' f) (cutaxA-left' f₁)
cutaxA-left' (∧l₁ f) = refl
cutaxA-left' (∧l₂ f) = refl
cutaxA-left' (∨r₁ f) = cong ∨r₁ (cutaxA-left' f)
cutaxA-left' (∨r₂ f) = cong ∨r₂ (cutaxA-left' f)
cutaxA-left' (∨l f f₁) = refl

cutaxA-left : ∀ {A C} (f : A ⊢ C) → cut ax f ≗ f
cutaxA-left f = ≡to≗ (cutaxA-left' f)

cutaxA-right : ∀ {A C} (f : A ⊢ C) → cut f ax ≗ f
cutaxA-right f = refl

g~ : ∀ {A C D} {g g' : A ⊢ D} {h : D ⊢ C}
  → {vg vg' : ∀ {X} → X ∈F D → X ∈F A}
  → {vh vh' : ∀ {X} → X ∈F D → X ∈F C}
  → g ≗ g'
  → intrp D g h vg vh ~ intrp D g' h vg' vh'
g~ {g = g} {h = h} p =
  ↝∷ (ax , (cutaxA-right g ∙ p) , (~ cutaxA-left h)) refl

h~ : ∀ {A C D} {g : A ⊢ D} {h h' : D ⊢ C}
  → {vg vg' : ∀ {X} → X ∈F D → X ∈F A}
  → {vh vh' : ∀ {X} → X ∈F D → X ∈F C}
  → h ≗ h'
  → intrp D g h vg vh ~ intrp D g h' vg' vh'
h~ {g = g} {h' = h'} p =
  ↝∷ (ax , cutaxA-right g , (p ∙ (~ cutaxA-left h'))) refl
