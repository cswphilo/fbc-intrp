
module FocusedSeqCalc where

open import Data.Empty
open import Data.Unit
open import Data.List 
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Utilities
open import Formulae
open import SeqCalc
open import Tags

{-
Definition of the focused calculus
-}
-- ri = right invertible
data _⊢ri_ : Fma → Fma → Set

-- l = left phase
data _⊢li_ : Fma → Pos → Set

-- f = focusing
data _⊢f_ : Neg → Pos → Set

tags-ri : (S : Neg) {C : Fma} → neg S ⊢ri C → List Tag
tag-f : {S : Neg} {C : Pos} → S ⊢f C → Tag

data _⊢ri_ where
  ∧r : {S A B : Fma}
    → (f : S ⊢ri A) (g : S ⊢ri B)
    ---------------------------------------
    →          S ⊢ri A ∧ B
    
  li2ri : {S : Fma} {C : Pos}
    → (f : S ⊢li C)
    ------------------------
    →      S ⊢ri pos C

data _⊢li_ where
  ∨l : {A B : Fma} {C : Pos}
      (f : A ⊢li C) (g : B ⊢li C) →
      -----------------------------------------
           A ∨ B ⊢li C
           
  f2li : {S : Neg} {C : Pos}
        (f : S ⊢f C) →
        --------------------------
             neg S ⊢li C

data _⊢f_ where
  ax : {X : At} →
       (mkNeg (` X) _) ⊢f (mkPos (` X) _)
  ∧l₁ : {A B : Fma} {C : Pos}
        (f : A ⊢li C) →
        --------------------------------
             (mkNeg (A ∧ B) _) ⊢f C
  ∧l₂ : {A B : Fma} {C : Pos}
        (f : B ⊢li C) →
        --------------------------------
             (mkNeg (A ∧ B) _) ⊢f C
  ∨r₁ : {S : Neg} {A B : Fma} →
        (f : neg S ⊢ri A) →
        (ok : isOK (tags-ri S f)) →
        -------------------------
             S ⊢f (mkPos (A ∨ B) _)
  ∨r₂ : {S : Neg} {A B : Fma} →
        (f : neg S ⊢ri B) →
        (ok : isOK (tags-ri S f)) →
        -------------------------
             S ⊢f (mkPos (A ∨ B) _)

tags-ri S (∧r f g) = tags-ri S f ++ tags-ri S g
tags-ri _ (li2ri (f2li f)) = [ tag-f f ]

tag-f ax = R
tag-f (∧l₁ f) = C₁
tag-f (∧l₂ f) = C₂
tag-f (∨r₁ f ok) = R
tag-f (∨r₂ f ok) = R


---------------------------


∨l-li-inv₁ : ∀ {A B C} → A ∨ B ⊢li C → A ⊢li C
∨l-li-inv₁ (∨l f g) = f

∨l-li-inv₂ : ∀ {A B C} → A ∨ B ⊢li C → B ⊢li C
∨l-li-inv₂ (∨l f g) = g



f2li-fs : {S : Neg} {Φ : Tree Pos}
  → All (λ P → S ⊢f P) Φ
  → All (λ P → neg S ⊢li P) Φ
f2li-fs = mapAll f2li

∧l₁-f-fs : ∀ {A B Φ}
  → All (λ P → A ⊢li P) Φ
  → All (λ P → (mkNeg (A ∧ B) _) ⊢f P) Φ
∧l₁-f-fs = mapAll ∧l₁

∧l₂-f-fs : ∀ {A B Φ}
  → All (λ P → B ⊢li P) Φ
  → All (λ P → (mkNeg (A ∧ B) _) ⊢f P) Φ
∧l₂-f-fs = mapAll ∧l₂

∨l-fs :  ∀ {A B Φ}
  → All (_⊢li_ A) Φ → All (_⊢li_ B) Φ
  → All (_⊢li_ (A ∨ B)) Φ
∨l-fs = map2All ∨l

∨l-inv-fs₁ : ∀ {A B Φ}
  → All (λ P → A ∨ B ⊢li P) Φ
  → All (λ P → A ⊢li P) Φ
∨l-inv-fs₁ = mapAll ∨l-li-inv₁

∨l-inv-fs₂ : ∀ {A B Φ}
  → All (λ P → A ∨ B ⊢li P) Φ
  → All (λ P → B ⊢li P) Φ
∨l-inv-fs₂ = mapAll ∨l-li-inv₂



∨r₂eq : {S : Neg} {A B : Fma} {f f' : neg S ⊢ri B} → f ≡ f'
  → {ok : isOK (tags-ri S f)} {ok' : isOK (tags-ri S f')}
  → ∨r₂ {A = A} f ok ≡ ∨r₂ f' ok'
∨r₂eq {f = f} refl = cong (∨r₂ _) (isProp-isOK (tags-ri _ f))

∨r₁eq : {S : Neg} {A B : Fma} {f f' : neg S ⊢ri A} → f ≡ f'
  → {ok : isOK (tags-ri S f)} {ok' : isOK (tags-ri S f')}
  → ∨r₁ {B = B} f ok ≡ ∨r₁ f' ok'
∨r₁eq {f = f} refl = cong (∨r₁ _) (isProp-isOK (tags-ri _ f))

---------------------------

tags-fs : (S : Neg) {Φ : Tree Pos} (fs : All (λ C → neg S ⊢li C) Φ) → List Tag
tags-fs _ (leaf (f2li f)) = [ tag-f f ]
tags-fs S (node fs fs') = tags-fs S fs ++ tags-fs S fs'

nonempty-tags-fs : {S : Neg} {Φ : Tree Pos} (fs : All (λ C → neg S ⊢li C) Φ) → tags-fs S fs ≡ [] → ⊥
nonempty-tags-fs (leaf (f2li f)) ()
nonempty-tags-fs {S} (node fs fs') eq = nonempty-tags-fs {S} fs (empty++1 _ eq)

tags-onlyC₁ : ∀ {A B Φ} (fs : All (_⊢li_ A) Φ) → onlyC₁ (tags-fs _ (f2li-fs (∧l₁-f-fs {B = B} fs)))
tags-onlyC₁ (leaf f) = tt
tags-onlyC₁ (node fs fs') = onlyC₁++ (tags-fs _ (f2li-fs (∧l₁-f-fs fs))) (tags-onlyC₁ fs) (tags-onlyC₁ fs')

tags-onlyC₂ : ∀ {A B Φ} (fs : All (_⊢li_ B) Φ) → onlyC₂ (tags-fs _ (f2li-fs (∧l₂-f-fs {A = A} fs)))
tags-onlyC₂ (leaf f) = tt
tags-onlyC₂ (node fs fs') = onlyC₂++ (tags-fs _ (f2li-fs (∧l₂-f-fs fs))) (tags-onlyC₂ fs) (tags-onlyC₂ fs')
