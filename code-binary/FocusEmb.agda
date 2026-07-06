module FocusEmb where

open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])

open import Utilities
open import Formulae
open import SeqCalc
open import Tags
open import FocusedSeqCalc
open import Focus
open import Emb

{-
We show that focused derivations are in normal form, 
i.e. running the noralization algorithm on a focused derivation would
obtain a syntactically identical derivation, i.e. focus (emb-ri f) ≡ f
-}


∨r₁-li-∧r*-ri-inv' : ∀ S {A B} (fs : All (_⊢li_ (neg S)) (toTree A)) (ok : isOK (tags-ri _ (∧r*-ri A fs)))
  → ∨r₁-li (neg S) {B = B} fs ≡ f2li {S} (∨r₁ (∧r*-ri A fs) ok)
∨r₁-li-neg-∧r*-ri-inv' : (S : Fma) .{i : isNeg S} {A B : Fma} (fs : All (_⊢li_ S) (toTree A)) (ok : isOK (tags-ri (mkNeg S i) (∧r*-ri A fs)))
  → (c : CheckFocus fs)
  → ∨r₁-li-neg S {B = B} fs c ≡ ∨r₁ (∧r*-ri A fs) ok
  
∨r₁-li-∧r*-ri-inv' (mkNeg (` X) _) fs ok = cong f2li (∨r₁-li-neg-∧r*-ri-inv' _ fs ok _)
∨r₁-li-∧r*-ri-inv' (mkNeg (A ∧ B) _) fs ok = cong f2li (∨r₁-li-neg-∧r*-ri-inv' _ fs ok _)

∨r₁-li-neg-∧r*-ri-inv' (` X) fs ok (caseok ok') = cong (∨r₁ (∧r*-ri _ fs)) (isProp-isOK (tags-ri _ (∧r*-ri _ fs)))
∨r₁-li-neg-∧r*-ri-inv' (S ∧ S') fs ok (case1 (all∧l₁ {B = B} gs refl refl)) =
  ⊥-elim (notOK-onlyC₁ (tags-fs _ (f2li-fs (∧l₁-f-fs {B = B} gs)))
                       (tags-onlyC₁ gs)
                       (subst isOK (sym (tags-ri∧r*-ri _ (f2li-fs (∧l₁-f-fs gs)))) ok ))
∨r₁-li-neg-∧r*-ri-inv' (S ∧ S') fs ok (case2 (all∧l₂ {A = A} gs refl refl)) = 
  ⊥-elim (notOK-onlyC₂ (tags-fs _ (f2li-fs (∧l₂-f-fs {A = A} gs)))
                       (tags-onlyC₂ gs)
                       (subst isOK (sym (tags-ri∧r*-ri _ (f2li-fs (∧l₂-f-fs gs)))) ok ))
∨r₁-li-neg-∧r*-ri-inv' (S ∧ S') fs ok (caseok ok') = cong (∨r₁ (∧r*-ri _ fs)) (isProp-isOK (tags-ri _ (∧r*-ri _ fs)))

∨r₁-li-∧r*-ri-inv : ∀ S {A B} (f : neg S ⊢ri A) (ok : isOK (tags-ri S f))
  → ∨r₁-li (neg S) {B = B} (∧r*-ri-inv f) ≡ f2li (∨r₁ f ok)
∨r₁-li-neg-∧r*-ri-inv : (S : Fma) .{i : isNeg S} {A B : Fma} (f : S ⊢ri A) (ok : isOK (tags-ri (mkNeg S i) f))
  → (c : CheckFocus (∧r*-ri-inv f))
  → ∨r₁-li-neg S {B = B} (∧r*-ri-inv f) c ≡ ∨r₁ f ok

∨r₁-li-∧r*-ri-inv (mkNeg (` X) isneg) f ok = cong f2li (∨r₁-li-neg-∧r*-ri-inv _ f ok _)
∨r₁-li-∧r*-ri-inv (mkNeg (S ∧ S') isneg) f ok = cong f2li (∨r₁-li-neg-∧r*-ri-inv _ f ok _)

∨r₁-li-neg-∧r*-ri-inv (` X) f ok (caseok _) = ∨r₁eq (∧r*∧r*-ri-inv f)
∨r₁-li-neg-∧r*-ri-inv (S ∧ S') f ok (case1 (all∧l₁ {B = B} gs refl eqf)) with trans (sym (∧r*∧r*-ri-inv f)) (cong (∧r*-ri _) eqf)
... | refl = 
  ⊥-elim (notOK-onlyC₁ (tags-fs _ (f2li-fs (∧l₁-f-fs {B = B} gs)))
                       (tags-onlyC₁ gs)
                       (subst isOK (sym (tags-ri∧r*-ri _ (f2li-fs (∧l₁-f-fs gs)))) ok ))
∨r₁-li-neg-∧r*-ri-inv (S ∧ S') f ok (case2 (all∧l₂ {A = A} gs refl eqf)) with trans (sym (∧r*∧r*-ri-inv f)) (cong (∧r*-ri _) eqf)
... | refl = 
  ⊥-elim (notOK-onlyC₂ (tags-fs _ (f2li-fs (∧l₂-f-fs {A = A} gs)))
                       (tags-onlyC₂ gs)
                       (subst isOK (sym (tags-ri∧r*-ri _ (f2li-fs (∧l₂-f-fs gs)))) ok ))
∨r₁-li-neg-∧r*-ri-inv (S ∧ S') f ok (caseok _) = ∨r₁eq (∧r*∧r*-ri-inv f)




∨r₂-li-∧r*-ri-inv' : ∀ S {A B} (fs : All (_⊢li_ (neg S)) (toTree B)) (ok : isOK (tags-ri _ (∧r*-ri B fs)))
  → ∨r₂-li (neg S) {A = A} fs ≡ f2li {S} (∨r₂ (∧r*-ri B fs) ok)
∨r₂-li-neg-∧r*-ri-inv' : (S : Fma) .{i : isNeg S} {A B : Fma} (fs : All (_⊢li_ S) (toTree B)) (ok : isOK (tags-ri (mkNeg S i) (∧r*-ri B fs)))
  → (c : CheckFocus fs)
  → ∨r₂-li-neg S {A = A} fs c ≡ ∨r₂ (∧r*-ri B fs) ok
  
∨r₂-li-∧r*-ri-inv' (mkNeg (` X) _) fs ok = cong f2li (∨r₂-li-neg-∧r*-ri-inv' _ fs ok _)
∨r₂-li-∧r*-ri-inv' (mkNeg (A ∧ B) _) fs ok = cong f2li (∨r₂-li-neg-∧r*-ri-inv' _ fs ok _)

∨r₂-li-neg-∧r*-ri-inv' (` X) fs ok (caseok ok') = cong (∨r₂ (∧r*-ri _ fs)) (isProp-isOK (tags-ri _ (∧r*-ri _ fs)))
∨r₂-li-neg-∧r*-ri-inv' (S ∧ S') fs ok (case1 (all∧l₁ {B = B} gs refl refl)) =
  ⊥-elim (notOK-onlyC₁ (tags-fs _ (f2li-fs (∧l₁-f-fs {B = B} gs)))
                       (tags-onlyC₁ gs)
                       (subst isOK (sym (tags-ri∧r*-ri _ (f2li-fs (∧l₁-f-fs gs)))) ok ))
∨r₂-li-neg-∧r*-ri-inv' (S ∧ S') fs ok (case2 (all∧l₂ {A = A} gs refl refl)) = 
  ⊥-elim (notOK-onlyC₂ (tags-fs _ (f2li-fs (∧l₂-f-fs {A = A} gs)))
                       (tags-onlyC₂ gs)
                       (subst isOK (sym (tags-ri∧r*-ri _ (f2li-fs (∧l₂-f-fs gs)))) ok ))
∨r₂-li-neg-∧r*-ri-inv' (S ∧ S') fs ok (caseok ok') = cong (∨r₂ (∧r*-ri _ fs)) (isProp-isOK (tags-ri _ (∧r*-ri _ fs)))

∨r₂-li-∧r*-ri-inv : ∀ S {A B} (f : neg S ⊢ri B) (ok : isOK (tags-ri S f))
  → ∨r₂-li (neg S) {A = A} (∧r*-ri-inv f) ≡ f2li (∨r₂ f ok)
∨r₂-li-neg-∧r*-ri-inv : (S : Fma) .{i : isNeg S} {A B : Fma} (f : S ⊢ri B) (ok : isOK (tags-ri (mkNeg S i) f))
  → (c : CheckFocus (∧r*-ri-inv f))
  → ∨r₂-li-neg S {A = A} (∧r*-ri-inv f) c ≡ ∨r₂ f ok

∨r₂-li-∧r*-ri-inv (mkNeg (` X) isneg) f ok = cong f2li (∨r₂-li-neg-∧r*-ri-inv _ f ok _)
∨r₂-li-∧r*-ri-inv (mkNeg (S ∧ S') isneg) f ok = cong f2li (∨r₂-li-neg-∧r*-ri-inv _ f ok _)

∨r₂-li-neg-∧r*-ri-inv (` X) f ok (caseok _) = ∨r₂eq (∧r*∧r*-ri-inv f)
∨r₂-li-neg-∧r*-ri-inv (S ∧ S') f ok (case1 (all∧l₁ {B = B} gs refl eqf)) with trans (sym (∧r*∧r*-ri-inv f)) (cong (∧r*-ri _) eqf)
... | refl = 
  ⊥-elim (notOK-onlyC₁ (tags-fs _ (f2li-fs (∧l₁-f-fs {B = B} gs)))
                       (tags-onlyC₁ gs)
                       (subst isOK (sym (tags-ri∧r*-ri _ (f2li-fs (∧l₁-f-fs gs)))) ok ))
∨r₂-li-neg-∧r*-ri-inv (S ∧ S') f ok (case2 (all∧l₂ {A = A} gs refl eqf)) with trans (sym (∧r*∧r*-ri-inv f)) (cong (∧r*-ri _) eqf)
... | refl = 
  ⊥-elim (notOK-onlyC₂ (tags-fs _ (f2li-fs (∧l₂-f-fs {A = A} gs)))
                       (tags-onlyC₂ gs)
                       (subst isOK (sym (tags-ri∧r*-ri _ (f2li-fs (∧l₂-f-fs gs)))) ok ))
∨r₂-li-neg-∧r*-ri-inv (S ∧ S') f ok (caseok _) = ∨r₂eq (∧r*∧r*-ri-inv f)



focusemb-f : {S : Neg} {C : Pos} (f : S ⊢f C) → focus (emb-f f) ≡ li2ri (f2li f)
focusemb-li : {S : Fma} {C : Pos} (f : S ⊢li C) → focus (emb-li f) ≡ li2ri f
focusemb-ri : {S C : Fma} (f : S ⊢ri C) → focus (emb-ri f) ≡ f

focusemb-f ax = refl
focusemb-f (∧l₁ f) = cong ∧l₁-ri (focusemb-li f)
focusemb-f (∧l₂ f) = cong ∧l₂-ri (focusemb-li f)
focusemb-f (∨r₁ f ok) = trans (cong ∨r₁-ri (focusemb-ri f)) (cong li2ri (∨r₁-li-∧r*-ri-inv _ _ ok))
focusemb-f (∨r₂ f ok) = trans (cong ∨r₂-ri (focusemb-ri f)) (cong li2ri (∨r₂-li-∧r*-ri-inv _ _ ok))

focusemb-li (∨l f g) = cong₂ ∨l-ri (focusemb-li f) (focusemb-li g)
focusemb-li (f2li f) = focusemb-f f
 
focusemb-ri (∧r f g) = cong₂ ∧r (focusemb-ri f) (focusemb-ri g)
focusemb-ri (li2ri f) = focusemb-li f                                   
