module Focus where

open import Data.List
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])

open import Utilities
open import Formulae
open import SeqCalc
open import FocusedSeqCalc
open import Tags

∧r*-ri : {S : Fma} (A : Fma) (fs : All (λ C → S ⊢li C) (toTree A)) → S ⊢ri A
∧r*-ri (A ∧ B) (node fs gs) = ∧r (∧r*-ri A fs) (∧r*-ri B gs)
∧r*-ri (` X) (leaf f) = li2ri f
∧r*-ri (A ∨ B) (leaf f) = li2ri f

∧r*-ri-inv : {S A : Fma} (f : S ⊢ri A) → All (λ C → S ⊢li C) (toTree A)
∧r*-ri-inv (∧r f g) = node (∧r*-ri-inv f) (∧r*-ri-inv g)
∧r*-ri-inv (li2ri {C = mkPos (` X) _} f) = leaf f
∧r*-ri-inv (li2ri {C = mkPos (A ∨ B) _} f) = leaf f

∧r*∧r*-ri-inv : {S A : Fma} (f : S ⊢ri A) → ∧r*-ri A (∧r*-ri-inv f) ≡ f
∧r*∧r*-ri-inv (∧r f f') = cong₂ ∧r (∧r*∧r*-ri-inv f) (∧r*∧r*-ri-inv f')
∧r*∧r*-ri-inv (li2ri {C = mkPos (` X) _} f) = refl
∧r*∧r*-ri-inv (li2ri {C = mkPos (A ∨ B) _} f) = refl

tags-ri∧r*-ri : ∀ {S} A (fs : All (_⊢li_ (neg S)) (toTree A))
   → tags-fs S fs ≡ tags-ri S (∧r*-ri A fs)
tags-ri∧r*-ri (` X) (leaf (f2li f)) = refl
tags-ri∧r*-ri (A ∧ B) (node fs gs) = cong₂ _++_ (tags-ri∧r*-ri A fs) (tags-ri∧r*-ri B gs)
tags-ri∧r*-ri (A ∨ B) (leaf (f2li f)) = refl

{-
Given a list of sequents in phase li,
the shape of the proof must be in one 
of three cases below:
i) All sequents are conclusion of ∧l₁.
ii) All sequents are conclusion of ∧l₂.
iv) The list of sequents can generate 
a list of sequents in phase fT.
-}


record All∧l₁ {S : Neg} {Φ : Tree Pos} (fs : All (λ C → neg S ⊢li C) Φ) : Set where
  constructor all∧l₁
  field
    {A B} : Fma
    gs : All (λ C → A ⊢li C) Φ
    eqS : neg S ≡ A ∧ B
    eqf : subst (λ x → All (λ P → x ⊢li P) Φ) eqS fs ≡ f2li-fs (∧l₁-f-fs {B = B} gs)

record All∧l₂ {S : Neg} {Φ : Tree Pos} (fs : All (λ C → neg S ⊢li C) Φ) : Set where
  constructor all∧l₂
  field
    {A B} : Fma
    gs : All (λ C → B ⊢li C) Φ
    eqS : neg S ≡ A ∧ B
    eqf : subst (λ x → All (λ P → x ⊢li P) Φ) eqS fs ≡ f2li-fs (∧l₂-f-fs {A = A} gs)

data CheckFocus {S : Neg} {Φ : Tree Pos} (fs : All (λ C → neg S ⊢li C) Φ) : Set where
  case1 : All∧l₁ {S} fs → CheckFocus fs
  case2 : All∧l₂ {S} fs → CheckFocus fs
  caseok : isOK (tags-fs S fs) → CheckFocus fs
  
open All∧l₁
open All∧l₂

check-focus : {S : Neg} {Φ : Tree Pos} (fs : All (λ C → neg S ⊢li C) Φ) → CheckFocus {S} fs
check-focus (leaf (f2li ax)) = caseok tt 
check-focus (leaf (f2li (∧l₁ f))) = case1 (all∧l₁ (leaf f) refl refl)
check-focus (leaf (f2li (∧l₂ f))) = case2 (all∧l₂ (leaf f) refl refl)
check-focus (leaf (f2li (∨r₁ f ok))) = caseok tt 
check-focus (leaf (f2li (∨r₂ f ok))) = caseok tt 
check-focus {S} (node fs fs') with check-focus {S} fs | check-focus {S} fs'
... | case1 (all∧l₁ gs refl refl) | case1 (all∧l₁ gs' refl refl) = case1 (all∧l₁ (node gs gs') refl refl)
... | case1 (all∧l₁ gs refl refl) | case2 (all∧l₂ {A}{B} gs' refl refl) =
  caseok (isOKC₁++C₂ (tags-fs _ (f2li-fs (∧l₁-f-fs gs))) (tags-onlyC₁ gs) (tags-onlyC₂ gs')
                     (nonempty-tags-fs {S} (f2li-fs (∧l₁-f-fs gs)))
                     (nonempty-tags-fs {S} (f2li-fs (∧l₂-f-fs gs'))))
... | case2 (all∧l₂ gs refl refl) | case1 (all∧l₁ gs' refl refl) = 
  caseok (isOKC₂++C₁ (tags-fs _ (f2li-fs (∧l₂-f-fs gs))) (tags-onlyC₂ gs) (tags-onlyC₁ gs')
                     (nonempty-tags-fs {S} (f2li-fs (∧l₂-f-fs gs)))
                     (nonempty-tags-fs {S} (f2li-fs (∧l₁-f-fs gs'))))
... | case2 (all∧l₂ gs refl refl) | case2 (all∧l₂ gs' refl refl) = case2 (all∧l₂ (node gs gs') refl refl)
... | _ | caseok ok = caseok (isOK++2 (tags-fs _ fs) ok)
... | caseok ok | _ = caseok (isOK++1 (tags-fs _ fs) ok)

∨r₁-li : (S : Fma) {A B : Fma} (fs : All (λ C → S ⊢li C) (toTree A)) → S ⊢li mkPos (A ∨ B) _
∨r₁-li-neg : (S : Fma) → .{i : isNeg S} → {A B : Fma} (fs : All (λ C → S ⊢li C) (toTree A)) 
  → CheckFocus {mkNeg S i} fs → (mkNeg S i) ⊢f mkPos (A ∨ B) _

∨r₁-li (` X) fs = f2li (∨r₁-li-neg _ fs (check-focus fs))
∨r₁-li (S ∧ S') fs = f2li (∨r₁-li-neg _ fs (check-focus fs))
∨r₁-li (S ∨ S') fs = ∨l (∨r₁-li S (∨l-inv-fs₁ fs)) (∨r₁-li S' (∨l-inv-fs₂ fs))

∨r₁-li-neg (` X) fs (caseok ok) = ∨r₁ (∧r*-ri _ fs) (subst isOK (tags-ri∧r*-ri _ fs) ok)
∨r₁-li-neg (S ∧ S') fs (case1 (all∧l₁ gs refl eqf)) = ∧l₁ (∨r₁-li S gs)
∨r₁-li-neg (S ∧ S') fs (case2 (all∧l₂ gs refl eqf)) = ∧l₂ (∨r₁-li S' gs)
∨r₁-li-neg (S ∧ S') fs (caseok ok) = ∨r₁ (∧r*-ri _ fs) (subst isOK (tags-ri∧r*-ri _ fs) ok)

∨r₂-li : (S : Fma) {A B : Fma} (fs : All (λ C → S ⊢li C) (toTree B)) → S ⊢li mkPos (A ∨ B) _
∨r₂-li-neg : (S : Fma) → .{i : isNeg S} → {A B : Fma} (fs : All (λ C → S ⊢li C) (toTree B)) 
  → CheckFocus {mkNeg S i} fs → (mkNeg S i) ⊢f mkPos (A ∨ B) _

∨r₂-li (` X) fs = f2li (∨r₂-li-neg _ fs (check-focus fs))
∨r₂-li (S ∧ S') fs = f2li (∨r₂-li-neg _ fs (check-focus fs))
∨r₂-li (S ∨ S') fs = ∨l (∨r₂-li S (∨l-inv-fs₁ fs)) (∨r₂-li S' (∨l-inv-fs₂ fs))

∨r₂-li-neg (` X) fs (caseok ok) = ∨r₂ (∧r*-ri _ fs) (subst isOK (tags-ri∧r*-ri _ fs) ok)
∨r₂-li-neg (S ∧ S') fs (case1 (all∧l₁ gs refl eqf)) = ∧l₁ (∨r₂-li S gs)
∨r₂-li-neg (S ∧ S') fs (case2 (all∧l₂ gs refl eqf)) = ∧l₂ (∨r₂-li S' gs)
∨r₂-li-neg (S ∧ S') fs (caseok ok) = ∨r₂ (∧r*-ri _ fs) (subst isOK (tags-ri∧r*-ri _ fs) ok)


∨r₁-ri : {S A B : Fma} (f : S ⊢ri A) → S ⊢ri A ∨ B
∨r₁-ri f = li2ri (∨r₁-li _ (∧r*-ri-inv f))

∨r₂-ri : {S A B : Fma} (f : S ⊢ri B) → S ⊢ri A ∨ B
∨r₂-ri f = li2ri (∨r₂-li _ (∧r*-ri-inv f))

∨l-ri :  {A B C : Fma} (f : A ⊢ri C) (g : B ⊢ri C) → A ∨ B ⊢ri C
∨l-ri (∧r f f₁) (∧r g g₁) = ∧r (∨l-ri f g) (∨l-ri f₁ g₁)
∨l-ri (li2ri f) (li2ri g) = li2ri (∨l f g)

∧l₁-ri :  {A B C : Fma} (f : A ⊢ri C) → A ∧ B ⊢ri C
∧l₁-ri (∧r f f') = ∧r (∧l₁-ri f) (∧l₁-ri f')
∧l₁-ri (li2ri f) = li2ri (f2li (∧l₁ f))

∧l₂-ri :  {A B C : Fma} (f : B ⊢ri C) → A ∧ B ⊢ri C
∧l₂-ri (∧r f f') = ∧r (∧l₂-ri f) (∧l₂-ri f')
∧l₂-ri (li2ri f) = li2ri (f2li (∧l₂ f))

ax-ri : (C : Fma) → C ⊢ri C
ax-ri (` X) = li2ri (f2li ax)
ax-ri (A ∧ B) = ∧r (∧l₁-ri (ax-ri A)) (∧l₂-ri (ax-ri B))
ax-ri (A ∨ B) = ∨l-ri (∨r₁-ri (ax-ri A)) (∨r₂-ri (ax-ri B))

-- focus function maps each derivation in SeqCalc to a focused derivation.
focus : {S C : Fma} → (f : S ⊢ C) → S ⊢ri C
focus ax = ax-ri _
focus (∧r f g) = ∧r (focus f) (focus g)
focus (∧l₁ f) = ∧l₁-ri (focus f)
focus (∧l₂ f) = ∧l₂-ri (focus f)
focus (∨r₁ f) = ∨r₁-ri (focus f)
focus (∨r₂ f) = ∨r₂-ri (focus f)
focus (∨l f g) = ∨l-ri (focus f) (focus g)
