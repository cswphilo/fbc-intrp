
module FocusWellDef where

open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])

open import Utilities
open import Formulae 
open import SeqCalc
open import Tags
open import FocusedSeqCalc
open import Focus


∧r*inv∧l₁-ri : {A B D : Fma} (f : A ⊢ri D)
  → ∧r*-ri-inv (∧l₁-ri {B = B} f) ≡ f2li-fs (∧l₁-f-fs (∧r*-ri-inv f))
∧r*inv∧l₁-ri (∧r f f') = cong₂ node (∧r*inv∧l₁-ri f) (∧r*inv∧l₁-ri f')
∧r*inv∧l₁-ri (li2ri {C = mkPos (` X) _} f) = refl
∧r*inv∧l₁-ri (li2ri {C = mkPos (A ∨ B) _} f) = refl

∧r*inv∧l₂-ri : {A B D : Fma} (f : B ⊢ri D)
  → ∧r*-ri-inv (∧l₂-ri {A = A} f) ≡ f2li-fs (∧l₂-f-fs (∧r*-ri-inv f))
∧r*inv∧l₂-ri (∧r f f') = cong₂ node (∧r*inv∧l₂-ri f) (∧r*inv∧l₂-ri f')
∧r*inv∧l₂-ri (li2ri {C = mkPos (` X) _} f) = refl
∧r*inv∧l₂-ri (li2ri {C = mkPos (A ∨ B) _} f) = refl

∧r*-inv∨l-ri : {A B C : Fma} (f : A ⊢ri C) (g : B ⊢ri C)
  → ∧r*-ri-inv (∨l-ri f g) ≡ ∨l-fs (∧r*-ri-inv f) (∧r*-ri-inv g)
∧r*-inv∨l-ri (∧r f f') (∧r g g') = cong₂ node (∧r*-inv∨l-ri f g) (∧r*-inv∨l-ri f' g')
∧r*-inv∨l-ri (li2ri {C = mkPos _ _} f) (li2ri {C = mkPos (` X) _} g) = refl
∧r*-inv∨l-ri (li2ri {C = mkPos _ _} f) (li2ri {C = mkPos (A ∨ B) _} g) = refl

∨l-inv-fs₁∨l-fs : {A B : Fma} {Φ : Tree Pos} (fs : All (_⊢li_ A) Φ) (gs : All (_⊢li_ B) Φ)
  → ∨l-inv-fs₁ (∨l-fs fs gs) ≡ fs
∨l-inv-fs₁∨l-fs (leaf f) (leaf g) = refl
∨l-inv-fs₁∨l-fs (node fs fs') (node gs gs') = cong₂ node (∨l-inv-fs₁∨l-fs fs gs) (∨l-inv-fs₁∨l-fs fs' gs')

∨l-inv-fs₂∨l-fs : {A B : Fma} {Φ : Tree Pos} (fs : All (_⊢li_ A) Φ) (gs : All (_⊢li_ B) Φ)
  → ∨l-inv-fs₂ (∨l-fs fs gs) ≡ gs
∨l-inv-fs₂∨l-fs (leaf f) (leaf g) = refl
∨l-inv-fs₂∨l-fs (node fs fs') (node gs gs') = cong₂ node (∨l-inv-fs₂∨l-fs fs gs) (∨l-inv-fs₂∨l-fs fs' gs')

check-focus-all∧l₁ : {A B : Fma} {Φ : Tree Pos}
  → (fs : All (λ C → A ⊢li C) Φ)
  → check-focus (f2li-fs (∧l₁-f-fs {B = B} fs)) ≡ case1 (all∧l₁ fs refl refl)
check-focus-all∧l₁ (leaf f) = refl
check-focus-all∧l₁ {B = B} (node fs fs') rewrite check-focus-all∧l₁ {B = B} fs | check-focus-all∧l₁ {B = B} fs' = refl

check-focus-all∧l₂ : {A B : Fma} {Φ : Tree Pos}
  → (fs : All (λ C → B ⊢li C) Φ)
  → check-focus (f2li-fs (∧l₂-f-fs {A = A} fs)) ≡ case2 (all∧l₂ fs refl refl)
check-focus-all∧l₂ (leaf f) = refl
check-focus-all∧l₂ {A = A} (node fs fs') rewrite check-focus-all∧l₂ {A = A} fs | check-focus-all∧l₂ {A = A} fs' = refl


∨r₁∧l₁-ri :  {A B D E : Fma} (f : A ⊢ri D)
  → ∨r₁-ri {B = E} (∧l₁-ri {B = B} f) ≡ ∧l₁-ri (∨r₁-ri f)
∨r₁∧l₁-ri {B = B} f =
  cong li2ri (cong f2li (trans (cong (λ x → ∨r₁-li-neg _ x (check-focus x)) (∧r*inv∧l₁-ri f))
                               (cong (∨r₁-li-neg _ (f2li-fs (∧l₁-f-fs (∧r*-ri-inv f)))) (check-focus-all∧l₁ _))))

∨r₁∧l₂-ri :  {A B D E : Fma} (f : B ⊢ri D)
  → ∨r₁-ri {B = E} (∧l₂-ri {A = A} f) ≡ ∧l₂-ri (∨r₁-ri f)
∨r₁∧l₂-ri {A = A} f =
  cong li2ri (cong f2li (trans (cong (λ x → ∨r₁-li-neg _ x (check-focus x)) (∧r*inv∧l₂-ri f))
                               (cong (∨r₁-li-neg _ (f2li-fs (∧l₂-f-fs (∧r*-ri-inv f)))) (check-focus-all∧l₂ _))))

∨r₂∧l₁-ri :  {A B D E : Fma} (f : A ⊢ri E)
  → ∨r₂-ri {A = D} (∧l₁-ri {B = B} f) ≡ ∧l₁-ri (∨r₂-ri f)
∨r₂∧l₁-ri {B = B} f = 
  cong li2ri (cong f2li (trans (cong (λ x → ∨r₂-li-neg _ x (check-focus x)) (∧r*inv∧l₁-ri f))
                               (cong (∨r₂-li-neg _ (f2li-fs (∧l₁-f-fs (∧r*-ri-inv f)))) (check-focus-all∧l₁ _))))

∨r₂∧l₂-ri :  {A B D E : Fma} (f : B ⊢ri E)
  → ∨r₂-ri {A = D} (∧l₂-ri {A = A} f) ≡ ∧l₂-ri (∨r₂-ri f)
∨r₂∧l₂-ri {A = A} f = 
  cong li2ri (cong f2li (trans (cong (λ x → ∨r₂-li-neg _ x (check-focus x)) (∧r*inv∧l₂-ri f))
                               (cong (∨r₂-li-neg _ (f2li-fs (∧l₂-f-fs (∧r*-ri-inv f)))) (check-focus-all∧l₂ _))))

∨r₁∨l-ri :  {A B C D : Fma}
  → (f : C ⊢ri A) (f' : D ⊢ri A)
  → ∨r₁-ri {B = B} (∨l-ri f f') ≡ ∨l-ri (∨r₁-ri f) (∨r₁-ri f')
∨r₁∨l-ri f f' =
  cong li2ri (cong₂ ∨l (cong (∨r₁-li _) (trans (cong ∨l-inv-fs₁ (∧r*-inv∨l-ri _ _)) (∨l-inv-fs₁∨l-fs _ _)))
                       (cong (∨r₁-li _) (trans (cong ∨l-inv-fs₂ (∧r*-inv∨l-ri _ _)) (∨l-inv-fs₂∨l-fs _ _))))

∨r₂∨l-ri :  {A B C D : Fma}
  → (f : C ⊢ri B) (f' : D ⊢ri B)
  → ∨r₂-ri {A = A} (∨l-ri f f') ≡ ∨l-ri (∨r₂-ri f) (∨r₂-ri f')
∨r₂∨l-ri f f' =
  cong li2ri (cong₂ ∨l (cong (∨r₂-li _) (trans (cong ∨l-inv-fs₁ (∧r*-inv∨l-ri _ _)) (∨l-inv-fs₁∨l-fs _ _)))
                       (cong (∨r₂-li _) (trans (cong ∨l-inv-fs₂ (∧r*-inv∨l-ri _ _)) (∨l-inv-fs₂∨l-fs _ _))))

-- equivalent derivations in SeqCalc are identical in focused calculus
eqfocus : ∀ {S C} {f f' : S ⊢ C} → f ≗ f' → focus f ≡ focus f'
eqfocus refl = refl
eqfocus (~ eq) = sym (eqfocus eq)
eqfocus (eq ∙ eq') = trans (eqfocus eq) (eqfocus eq')
eqfocus (∧r eq eq') = cong₂ (λ x y → ∧r x y) (eqfocus eq) (eqfocus eq')
eqfocus (∧l₁ eq) = cong ∧l₁-ri (eqfocus eq)
eqfocus (∧l₂ eq) = cong ∧l₂-ri (eqfocus eq)
eqfocus ax∧ = refl
eqfocus ax∨ = refl
eqfocus ∧r∧l₁ = refl
eqfocus ∧r∧l₂ = refl
eqfocus ∧r∨l = refl
eqfocus (∨r₁ eq) = cong ∨r₁-ri (eqfocus eq)
eqfocus (∨r₂ eq) = cong ∨r₂-ri (eqfocus eq)
eqfocus (∨l eq1 eq2) = cong₂ (λ x y → ∨l-ri x y) (eqfocus eq1) (eqfocus eq2)
eqfocus (∨r₁∧l₁ {f = f}) = ∨r₁∧l₁-ri (focus f)
eqfocus (∨r₁∧l₂ {f = f}) = ∨r₁∧l₂-ri (focus f)
eqfocus (∨r₁∨l {f = f} {g}) = ∨r₁∨l-ri (focus f) (focus g)
eqfocus (∨r₂∧l₁ {f = f}) = ∨r₂∧l₁-ri (focus f)
eqfocus (∨r₂∧l₂ {f = f}) = ∨r₂∧l₂-ri (focus f)
eqfocus (∨r₂∨l {f = f} {g}) = ∨r₂∨l-ri (focus f) (focus g)                 




