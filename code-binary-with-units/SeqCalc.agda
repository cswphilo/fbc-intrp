
module SeqCalc where

-- open import Data.List
open import Relation.Binary.PropositionalEquality hiding (_≗_)

-- open import Utilities
open import Formulae

-- =======================================================================

-- Sequent calculus

infix 15 _⊢_

data _⊢_ : Fma → Fma → Set where
  ax : {A : Fma} → A ⊢ A
  ⊤r : {S : Fma} → S ⊢ ⊤
  ⊥l : {C : Fma} → ⊥ ⊢ C
  ∧r : {S A B : Fma} → 
              S ⊢ A → S ⊢ B → 
              S ⊢ A ∧ B
  ∧l₁ : {A B C : Fma} → 
              A ⊢ C → 
              A ∧ B ⊢ C
  ∧l₂ : {A B C : Fma} → 
              B ⊢ C → 
              A ∧ B ⊢ C
  ∨r₁ : {S A B : Fma} → 
              S ⊢ A → 
              S ⊢ A ∨ B
  ∨r₂ : {S A B : Fma} → 
              S ⊢ B → 
              S ⊢ A ∨ B
  ∨l : {A B C : Fma} → 
              A ⊢ C → B ⊢ C → 
              A ∨ B ⊢ C

-- ====================================================================

-- Equality of proofs 

infixl 15 _∙_

data _≗_ : {S A : Fma} → S ⊢ A → S ⊢ A → Set where

-- -- equivalence relation
  refl : ∀{S A} {f : S ⊢ A} → f ≗ f
  ~_ : ∀{S A} {f g : S ⊢ A} → f ≗ g → g ≗ f
  _∙_ : ∀{S A} {f g h : S ⊢ A} → f ≗ g → g ≗ h → f ≗ h

-- -- congruence
  ∧r : ∀{S A B} {f g : S ⊢ A} {f' g' : S ⊢ B} 
    → f ≗ g → f' ≗ g' → ∧r f f' ≗ ∧r g g'
  ∧l₁ : ∀{A B C} {f g : A ⊢ C}
     → f ≗ g → (∧l₁ {B = B} f) ≗ ∧l₁ g
  ∧l₂ : ∀{A B C} {f g : B ⊢ C} 
    → f ≗ g → (∧l₂ {A = A} f) ≗ ∧l₂ g
  ∨r₁ : ∀ {S A B} {f g : S ⊢ A} 
    → f ≗ g → ∨r₁ {B = B} f ≗ ∨r₁ g
  ∨r₂ : ∀ {S A B} {f g : S ⊢ B} 
    → f ≗ g → ∨r₂ {A = A} f ≗ ∨r₂ g
  ∨l : ∀ {A B C} {f g : A ⊢ C} {f' g' : B ⊢ C}
    → f ≗ g → f' ≗ g'
    → ∨l f f' ≗ ∨l g g'

-- -- η-conversions
  ax∧ : {A B : Fma} → ax {A ∧ B} ≗ ∧r (∧l₁ ax) (∧l₂ ax)
  ax∨ : {A B : Fma} → ax {A ∨ B} ≗ ∨l (∨r₁ ax) (∨r₂ ax)

-- -- permutative conversions
  ∧r∧l₁ : {A A' B B' : Fma}
    → {f : A' ⊢ A} {g : A' ⊢ B}
    → ∧r (∧l₁ {B = B'} f) (∧l₁ g) ≗ ∧l₁ (∧r f g)
  ∧r∧l₂ : {A A' B B' : Fma}
    → {f : B' ⊢ A} {g : B' ⊢ B}
    → ∧r (∧l₂ {A = A'} f) (∧l₂ g) ≗ ∧l₂ (∧r f g)
  ∧r∨l : {A A' B B' : Fma} 
    → {f : A' ⊢ A} {f' : A' ⊢ B} {g : B' ⊢ A} {g' : B' ⊢ B}
    → ∧r (∨l f g) (∨l f' g') ≗ ∨l (∧r f f') (∧r g g')
  ∨r₁∧l₁ : {A A' B B' : Fma} 
    → {f : A' ⊢ A}
    → ∨r₁ {B = B} (∧l₁ {B = B'} f) ≗ ∧l₁ (∨r₁ f)
  ∨r₁∧l₂ : {A A' B B' : Fma} 
    → {f : B' ⊢ A}
    → ∨r₁ {B = B} (∧l₂ {A = A'} f) ≗ ∧l₂ (∨r₁ f)
  ∨r₁∨l : {A A' B B' : Fma}
    → {f : A' ⊢ A} {g : B' ⊢ A}
    → ∨r₁ {B = B} (∨l f g) ≗ ∨l (∨r₁ f) (∨r₁ g)
  ∨r₂∧l₁ : {A A' B B' : Fma} 
    → {f : A' ⊢ B}
    → ∨r₂ {A = A} (∧l₁ {B = B'} f) ≗ ∧l₁ (∨r₂ f)
  ∨r₂∧l₂ : {A A' B B' : Fma} 
    → {f : B' ⊢ B}
    → ∨r₂ {A = A} (∧l₂ {A = A'} f) ≗ ∧l₂ (∨r₂ f)
  ∨r₂∨l : {A A' B B' : Fma}
    → {f : A' ⊢ B} {g : B' ⊢ B}
    → ∨r₂ {A = A} (∨l f g) ≗ ∨l (∨r₂ f) (∨r₂ g)
  ⊤rf : {S : Fma}
    → {f : S ⊢ ⊤}
    → f ≗ ⊤r
  ⊥lf : {C : Fma}
    → {f : ⊥ ⊢ C}
    → f ≗ ⊥l
    
≡to≗ : {S C : Fma}
  → {f g : S ⊢ C}
  → f ≡ g
  → f ≗ g
≡to≗ refl = refl


{-
∨l-inv₁ : {A B C : Fma} → A ∨ B ⊢ C → A ⊢ C
∨l-inv₁ ax = ∨r₁ ax
∨l-inv₁ ⊤r = ⊤r
∨l-inv₁ (∧r f g) = ∧r (∨l-inv₁ f) (∨l-inv₁ g)
∨l-inv₁ (∨r₁ f) = ∨r₁ (∨l-inv₁ f)
∨l-inv₁ (∨r₂ f) = ∨r₂ (∨l-inv₁ f)
∨l-inv₁ (∨l f g) = f

∨l-inv₂ : {A B C : Fma} → A ∨ B ⊢ C → B ⊢ C
∨l-inv₂ ax = ∨r₂ ax
∨l-inv₂ ⊤r = ⊤r
∨l-inv₂ (∧r f g) = ∧r (∨l-inv₂ f) (∨l-inv₂ g)
∨l-inv₂ (∨r₁ f) = ∨r₁ (∨l-inv₂ f)
∨l-inv₂ (∨r₂ f) = ∨r₂ (∨l-inv₂ f)
∨l-inv₂ (∨l f g) = g

∧r* : {S : Fma} (A : Fma) (fs : All (λ C → S ⊢ pos C) (toTree A)) → S ⊢ A
∧r* (` X) (leaf f) = f
∧r* (A ∧ B) (node fs gs) = ∧r (∧r* A fs) (∧r* B gs)
∧r* (A ∨ B) (leaf f) = f

∧r*∧l₁ :  {A B C : Fma} (fs : All (λ D → A ⊢ pos D) (toTree C)) 
  → ∧r* C (mapAll ∧l₁ fs) ≗ ∧l₁ {B = B} (∧r* C fs)
∧r*∧l₁ {C = ` X} (leaf f) = refl
∧r*∧l₁ {C = C ∧ D} (node fs gs) = ∧r (∧r*∧l₁ fs) (∧r*∧l₁ gs) ∙ ∧r∧l₁
∧r*∧l₁ {C = C ∨ D} (leaf f) = refl

∧r*∧l₂ :  {A B C : Fma} (fs : All (λ D → B ⊢ pos D) (toTree C)) 
  → ∧r* C (mapAll ∧l₂ fs) ≗ ∧l₂ {A = A} (∧r* C fs)
∧r*∧l₂ {C = ` X} (leaf f) = refl
∧r*∧l₂ {C = C ∧ D} (node fs gs) = ∧r (∧r*∧l₂ fs) (∧r*∧l₂ gs) ∙ ∧r∧l₂
∧r*∧l₂ {C = C ∨ D} (leaf f) = refl

∧r*∨l : {A B C : Fma}
  → (fs : All (λ E → A ⊢ pos E) (toTree C)) (gs : All (λ E → B ⊢ pos E) (toTree C))
  → ∧r* C (map2All ∨l fs gs) ≗ ∨l (∧r* C fs) (∧r* C gs)
∧r*∨l {C = C ∧ D} (node fs fs') (node gs gs') =
  ∧r (∧r*∨l fs gs) (∧r*∨l fs' gs') ∙ ∧r∨l
∧r*∨l {C = ` X} (leaf f) (leaf g) = refl
∧r*∨l {C = C ∨ D} (leaf f) (leaf g) = refl
-}
