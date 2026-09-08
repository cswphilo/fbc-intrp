module CutProperties where

open import Relation.Binary.PropositionalEquality hiding (_≗_)
open import Formulae 
open import SeqCalc
open import Cut

cut∧l₁≗ : ∀ {A A' B C}
  → (f : A ⊢ B) (g : B ⊢ C)
  → cut (∧l₁ {B = A'} f) g ≗ ∧l₁ (cut f g)
cut∧l₁≗ f ax = refl
cut∧l₁≗ f ⊤r = ~ ⊤rf
cut∧l₁≗ f ⊥l = refl
cut∧l₁≗ f (∧r g g₁) = ∧r (cut∧l₁≗ f g) (cut∧l₁≗ f g₁) ∙ ∧r∧l₁
cut∧l₁≗ f (∧l₁ g) = refl
cut∧l₁≗ f (∧l₂ g) = refl
cut∧l₁≗ f (∨r₁ g) = ∨r₁ (cut∧l₁≗ f g) ∙ ∨r₁∧l₁
cut∧l₁≗ f (∨r₂ g) = ∨r₂ (cut∧l₁≗ f g) ∙ ∨r₂∧l₁
cut∧l₁≗ f (∨l g g₁) = refl

cut∧l₂≗ : ∀ {A A' B C}
  → (f : A' ⊢ B) (g : B ⊢ C)
  → cut (∧l₂ {A = A} f) g ≗ ∧l₂ (cut f g)
cut∧l₂≗ f ax = refl
cut∧l₂≗ f ⊤r = ~ ⊤rf
cut∧l₂≗ f ⊥l = refl
cut∧l₂≗ f (∧r g g₁) = ∧r (cut∧l₂≗ f g) (cut∧l₂≗ f g₁) ∙ ∧r∧l₂
cut∧l₂≗ f (∧l₁ g) = refl
cut∧l₂≗ f (∧l₂ g) = refl
cut∧l₂≗ f (∨r₁ g) = ∨r₁ (cut∧l₂≗ f g) ∙ ∨r₁∧l₂
cut∧l₂≗ f (∨r₂ g) = ∨r₂ (cut∧l₂≗ f g) ∙ ∨r₂∧l₂
cut∧l₂≗ f (∨l g g₁) = refl

cut∨l≗ : ∀ {A A' B C}
  → (f : A ⊢ B) (f' : A' ⊢ B) (g : B ⊢ C)
  → cut (∨l f f') g ≗ ∨l (cut f g) (cut f' g)
cut∨l≗ f f' ax = refl
cut∨l≗ f f' ⊤r = ~ ⊤rf
cut∨l≗ f f' ⊥l = refl
cut∨l≗ f f' (∧r g g₁) =
  ∧r (cut∨l≗ f f' g) (cut∨l≗ f f' g₁) ∙ ∧r∨l
cut∨l≗ f f' (∧l₁ g) = refl
cut∨l≗ f f' (∧l₂ g) = refl
cut∨l≗ f f' (∨r₁ g) = ∨r₁ (cut∨l≗ f f' g) ∙ ∨r₁∨l
cut∨l≗ f f' (∨r₂ g) = ∨r₂ (cut∨l≗ f f' g) ∙ ∨r₂∨l
cut∨l≗ f f' (∨l g g₁) = refl

cut-assoc' : ∀ {A B C D}
  → (f : A ⊢ B) (g : B ⊢ C) (h : C ⊢ D)
  → cut (cut f g) h ≡ cut f (cut g h)
cut-assoc' f g ax = refl
cut-assoc' f g ⊤r = refl
cut-assoc' f g (∧r h h₁) = cong₂ ∧r (cut-assoc' f g h) (cut-assoc' f g h₁)
cut-assoc' f g (∨r₁ h) = cong ∨r₁ (cut-assoc' f g h)
cut-assoc' f g (∨r₂ h) = cong ∨r₂ (cut-assoc' f g h)
cut-assoc' f ax ⊥l = refl
cut-assoc' ax ⊥l ⊥l = refl
cut-assoc' ⊥l ⊥l ⊥l = refl
cut-assoc' (∧l₁ f) ⊥l ⊥l = cong ∧l₁ (cut-assoc' f ⊥l ⊥l)
cut-assoc' (∧l₂ f) ⊥l ⊥l = cong ∧l₂ (cut-assoc' f ⊥l ⊥l)
cut-assoc' (∨l f f₁) ⊥l ⊥l = cong₂ ∨l (cut-assoc' f ⊥l ⊥l) (cut-assoc' f₁ ⊥l ⊥l)
cut-assoc' ax (∧l₁ g) ⊥l = refl
cut-assoc' ⊥l (∧l₁ g) ⊥l = refl
cut-assoc' (∧r f f₁) (∧l₁ g) ⊥l = cut-assoc' f g ⊥l
cut-assoc' (∧l₁ f) (∧l₁ g) ⊥l = cong ∧l₁ (cut-assoc' f (∧l₁ g) ⊥l)
cut-assoc' (∧l₂ f) (∧l₁ g) ⊥l = cong ∧l₂ (cut-assoc' f (∧l₁ g) ⊥l)
cut-assoc' (∨l f f₁) (∧l₁ g) ⊥l =
  cong₂ ∨l (cut-assoc' f (∧l₁ g) ⊥l) (cut-assoc' f₁ (∧l₁ g) ⊥l)
cut-assoc' ax (∧l₂ g) ⊥l = refl
cut-assoc' ⊥l (∧l₂ g) ⊥l = refl
cut-assoc' (∧r f f₁) (∧l₂ g) ⊥l = cut-assoc' f₁ g ⊥l
cut-assoc' (∧l₁ f) (∧l₂ g) ⊥l = cong ∧l₁ (cut-assoc' f (∧l₂ g) ⊥l)
cut-assoc' (∧l₂ f) (∧l₂ g) ⊥l = cong ∧l₂ (cut-assoc' f (∧l₂ g) ⊥l)
cut-assoc' (∨l f f₁) (∧l₂ g) ⊥l =
  cong₂ ∨l (cut-assoc' f (∧l₂ g) ⊥l) (cut-assoc' f₁ (∧l₂ g) ⊥l)
cut-assoc' ax (∨l g g₁) ⊥l = refl
cut-assoc' ⊥l (∨l g g₁) ⊥l = refl
cut-assoc' (∧l₁ f) (∨l g g₁) ⊥l = cong ∧l₁ (cut-assoc' f (∨l g g₁) ⊥l)
cut-assoc' (∧l₂ f) (∨l g g₁) ⊥l = cong ∧l₂ (cut-assoc' f (∨l g g₁) ⊥l)
cut-assoc' (∨r₁ f) (∨l g g₁) ⊥l = cut-assoc' f g ⊥l
cut-assoc' (∨r₂ f) (∨l g g₁) ⊥l = cut-assoc' f g₁ ⊥l
cut-assoc' (∨l f f₁) (∨l g g₁) ⊥l =
  cong₂ ∨l (cut-assoc' f (∨l g g₁) ⊥l) (cut-assoc' f₁ (∨l g g₁) ⊥l)
cut-assoc' f ax (∧l₁ h) = refl
cut-assoc' ax ⊥l (∧l₁ h) = refl
cut-assoc' ⊥l ⊥l (∧l₁ h) = refl
cut-assoc' (∧l₁ f) ⊥l (∧l₁ h) = cong ∧l₁ (cut-assoc' f ⊥l (∧l₁ h))
cut-assoc' (∧l₂ f) ⊥l (∧l₁ h) = cong ∧l₂ (cut-assoc' f ⊥l (∧l₁ h))
cut-assoc' (∨l f f₁) ⊥l (∧l₁ h) =
  cong₂ ∨l (cut-assoc' f ⊥l (∧l₁ h)) (cut-assoc' f₁ ⊥l (∧l₁ h))
cut-assoc' f (∧r g g₁) (∧l₁ h) = cut-assoc' f g h
cut-assoc' ax (∧l₁ g) (∧l₁ h) = refl
cut-assoc' ⊥l (∧l₁ g) (∧l₁ h) = refl
cut-assoc' (∧r f f₁) (∧l₁ g) (∧l₁ h) = cut-assoc' f g (∧l₁ h)
cut-assoc' (∧l₁ f) (∧l₁ g) (∧l₁ h) =
  cong ∧l₁ (cut-assoc' f (∧l₁ g) (∧l₁ h))
cut-assoc' (∧l₂ f) (∧l₁ g) (∧l₁ h) =
  cong ∧l₂ (cut-assoc' f (∧l₁ g) (∧l₁ h))
cut-assoc' (∨l f f₁) (∧l₁ g) (∧l₁ h) =
  cong₂ ∨l (cut-assoc' f (∧l₁ g) (∧l₁ h))
           (cut-assoc' f₁ (∧l₁ g) (∧l₁ h))
cut-assoc' ax (∧l₂ g) (∧l₁ h) = refl
cut-assoc' ⊥l (∧l₂ g) (∧l₁ h) = refl
cut-assoc' (∧r f f₁) (∧l₂ g) (∧l₁ h) = cut-assoc' f₁ g (∧l₁ h)
cut-assoc' (∧l₁ f) (∧l₂ g) (∧l₁ h) =
  cong ∧l₁ (cut-assoc' f (∧l₂ g) (∧l₁ h))
cut-assoc' (∧l₂ f) (∧l₂ g) (∧l₁ h) =
  cong ∧l₂ (cut-assoc' f (∧l₂ g) (∧l₁ h))
cut-assoc' (∨l f f₁) (∧l₂ g) (∧l₁ h) =
  cong₂ ∨l (cut-assoc' f (∧l₂ g) (∧l₁ h))
           (cut-assoc' f₁ (∧l₂ g) (∧l₁ h))
cut-assoc' ax (∨l g g₁) (∧l₁ h) = refl
cut-assoc' ⊥l (∨l g g₁) (∧l₁ h) = refl
cut-assoc' (∧l₁ f) (∨l g g₁) (∧l₁ h) =
  cong ∧l₁ (cut-assoc' f (∨l g g₁) (∧l₁ h))
cut-assoc' (∧l₂ f) (∨l g g₁) (∧l₁ h) =
  cong ∧l₂ (cut-assoc' f (∨l g g₁) (∧l₁ h))
cut-assoc' (∨r₁ f) (∨l g g₁) (∧l₁ h) = cut-assoc' f g (∧l₁ h)
cut-assoc' (∨r₂ f) (∨l g g₁) (∧l₁ h) = cut-assoc' f g₁ (∧l₁ h)
cut-assoc' (∨l f f₁) (∨l g g₁) (∧l₁ h) =
  cong₂ ∨l (cut-assoc' f (∨l g g₁) (∧l₁ h))
           (cut-assoc' f₁ (∨l g g₁) (∧l₁ h))
cut-assoc' f ax (∧l₂ h) = refl
cut-assoc' ax ⊥l (∧l₂ h) = refl
cut-assoc' ⊥l ⊥l (∧l₂ h) = refl
cut-assoc' (∧l₁ f) ⊥l (∧l₂ h) = cong ∧l₁ (cut-assoc' f ⊥l (∧l₂ h))
cut-assoc' (∧l₂ f) ⊥l (∧l₂ h) = cong ∧l₂ (cut-assoc' f ⊥l (∧l₂ h))
cut-assoc' (∨l f f₁) ⊥l (∧l₂ h) =
  cong₂ ∨l (cut-assoc' f ⊥l (∧l₂ h)) (cut-assoc' f₁ ⊥l (∧l₂ h))
cut-assoc' f (∧r g g₁) (∧l₂ h) = cut-assoc' f g₁ h
cut-assoc' ax (∧l₁ g) (∧l₂ h) = refl
cut-assoc' ⊥l (∧l₁ g) (∧l₂ h) = refl
cut-assoc' (∧r f f₁) (∧l₁ g) (∧l₂ h) = cut-assoc' f g (∧l₂ h)
cut-assoc' (∧l₁ f) (∧l₁ g) (∧l₂ h) =
  cong ∧l₁ (cut-assoc' f (∧l₁ g) (∧l₂ h))
cut-assoc' (∧l₂ f) (∧l₁ g) (∧l₂ h) =
  cong ∧l₂ (cut-assoc' f (∧l₁ g) (∧l₂ h))
cut-assoc' (∨l f f₁) (∧l₁ g) (∧l₂ h) =
  cong₂ ∨l (cut-assoc' f (∧l₁ g) (∧l₂ h))
           (cut-assoc' f₁ (∧l₁ g) (∧l₂ h))
cut-assoc' ax (∧l₂ g) (∧l₂ h) = refl
cut-assoc' ⊥l (∧l₂ g) (∧l₂ h) = refl
cut-assoc' (∧r f f₁) (∧l₂ g) (∧l₂ h) = cut-assoc' f₁ g (∧l₂ h)
cut-assoc' (∧l₁ f) (∧l₂ g) (∧l₂ h) =
  cong ∧l₁ (cut-assoc' f (∧l₂ g) (∧l₂ h))
cut-assoc' (∧l₂ f) (∧l₂ g) (∧l₂ h) =
  cong ∧l₂ (cut-assoc' f (∧l₂ g) (∧l₂ h))
cut-assoc' (∨l f f₁) (∧l₂ g) (∧l₂ h) =
  cong₂ ∨l (cut-assoc' f (∧l₂ g) (∧l₂ h))
           (cut-assoc' f₁ (∧l₂ g) (∧l₂ h))
cut-assoc' ax (∨l g g₁) (∧l₂ h) = refl
cut-assoc' ⊥l (∨l g g₁) (∧l₂ h) = refl
cut-assoc' (∧l₁ f) (∨l g g₁) (∧l₂ h) =
  cong ∧l₁ (cut-assoc' f (∨l g g₁) (∧l₂ h))
cut-assoc' (∧l₂ f) (∨l g g₁) (∧l₂ h) =
  cong ∧l₂ (cut-assoc' f (∨l g g₁) (∧l₂ h))
cut-assoc' (∨r₁ f) (∨l g g₁) (∧l₂ h) = cut-assoc' f g (∧l₂ h)
cut-assoc' (∨r₂ f) (∨l g g₁) (∧l₂ h) = cut-assoc' f g₁ (∧l₂ h)
cut-assoc' (∨l f f₁) (∨l g g₁) (∧l₂ h) =
  cong₂ ∨l (cut-assoc' f (∨l g g₁) (∧l₂ h))
           (cut-assoc' f₁ (∨l g g₁) (∧l₂ h))
cut-assoc' f ax (∨l h h₁) = refl
cut-assoc' ax ⊥l (∨l h h₁) = refl
cut-assoc' ⊥l ⊥l (∨l h h₁) = refl
cut-assoc' (∧l₁ f) ⊥l (∨l h h₁) = cong ∧l₁ (cut-assoc' f ⊥l (∨l h h₁))
cut-assoc' (∧l₂ f) ⊥l (∨l h h₁) = cong ∧l₂ (cut-assoc' f ⊥l (∨l h h₁))
cut-assoc' (∨l f f₁) ⊥l (∨l h h₁) =
  cong₂ ∨l (cut-assoc' f ⊥l (∨l h h₁)) (cut-assoc' f₁ ⊥l (∨l h h₁))
cut-assoc' f (∨r₁ g) (∨l h h₁) = cut-assoc' f g h
cut-assoc' f (∨r₂ g) (∨l h h₁) = cut-assoc' f g h₁
cut-assoc' ax (∧l₁ g) (∨l h h₁) = refl
cut-assoc' ⊥l (∧l₁ g) (∨l h h₁) = refl
cut-assoc' (∧r f f₁) (∧l₁ g) (∨l h h₁) = cut-assoc' f g (∨l h h₁)
cut-assoc' (∧l₁ f) (∧l₁ g) (∨l h h₁) =
  cong ∧l₁ (cut-assoc' f (∧l₁ g) (∨l h h₁))
cut-assoc' (∧l₂ f) (∧l₁ g) (∨l h h₁) =
  cong ∧l₂ (cut-assoc' f (∧l₁ g) (∨l h h₁))
cut-assoc' (∨l f f₁) (∧l₁ g) (∨l h h₁) =
  cong₂ ∨l (cut-assoc' f (∧l₁ g) (∨l h h₁))
           (cut-assoc' f₁ (∧l₁ g) (∨l h h₁))
cut-assoc' ax (∧l₂ g) (∨l h h₁) = refl
cut-assoc' ⊥l (∧l₂ g) (∨l h h₁) = refl
cut-assoc' (∧r f f₁) (∧l₂ g) (∨l h h₁) = cut-assoc' f₁ g (∨l h h₁)
cut-assoc' (∧l₁ f) (∧l₂ g) (∨l h h₁) =
  cong ∧l₁ (cut-assoc' f (∧l₂ g) (∨l h h₁))
cut-assoc' (∧l₂ f) (∧l₂ g) (∨l h h₁) =
  cong ∧l₂ (cut-assoc' f (∧l₂ g) (∨l h h₁))
cut-assoc' (∨l f f₁) (∧l₂ g) (∨l h h₁) =
  cong₂ ∨l (cut-assoc' f (∧l₂ g) (∨l h h₁))
           (cut-assoc' f₁ (∧l₂ g) (∨l h h₁))
cut-assoc' ax (∨l g g₁) (∨l h h₁) = refl
cut-assoc' ⊥l (∨l g g₁) (∨l h h₁) = refl
cut-assoc' (∧l₁ f) (∨l g g₁) (∨l h h₁) =
  cong ∧l₁ (cut-assoc' f (∨l g g₁) (∨l h h₁))
cut-assoc' (∧l₂ f) (∨l g g₁) (∨l h h₁) =
  cong ∧l₂ (cut-assoc' f (∨l g g₁) (∨l h h₁))
cut-assoc' (∨r₁ f) (∨l g g₁) (∨l h h₁) = cut-assoc' f g (∨l h h₁)
cut-assoc' (∨r₂ f) (∨l g g₁) (∨l h h₁) = cut-assoc' f g₁ (∨l h h₁)
cut-assoc' (∨l f f₁) (∨l g g₁) (∨l h h₁) =
  cong₂ ∨l (cut-assoc' f (∨l g g₁) (∨l h h₁))
           (cut-assoc' f₁ (∨l g g₁) (∨l h h₁))

cut-assoc : ∀ {A B C D}
  → (f : A ⊢ B) (g : B ⊢ C) (h : C ⊢ D)
  → cut (cut f g) h ≗ cut f (cut g h)
cut-assoc f g h = ≡to≗ (cut-assoc' f g h)