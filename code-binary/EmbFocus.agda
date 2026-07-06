
module EmbFocus where

open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])

open import Utilities
open import Formulae
open import SeqCalc
open import Tags
open import FocusedSeqCalc
open import Focus
open import Emb

emb-li-fs : {S : Fma} {Φ : Tree Pos} (fs : All (λ C → S ⊢li C) Φ) → All (λ C → S ⊢ pos C) Φ
emb-li-fs = mapAll emb-li

emb-ri-∧r*-ri : {S : Fma} (A : Fma) (fs : All (λ C → S ⊢li C) (toTree A))
  → emb-ri (∧r*-ri A fs) ≗ ∧r* A (emb-li-fs fs)
emb-ri-∧r*-ri (` X) (leaf f) = refl
emb-ri-∧r*-ri (A ∧ B) (node fs gs) = ∧r (emb-ri-∧r*-ri A fs) (emb-ri-∧r*-ri B gs)
emb-ri-∧r*-ri (A ∨ B) (leaf f) = refl

emb∨r₁-li : (S : Fma) {A B : Fma} (fs : All (λ C → S ⊢li C) (toTree A))
  → emb-li (∨r₁-li S {B = B} fs) ≗ ∨r₁ (∧r* _ (emb-li-fs fs))
emb∨r₁-li-neg : (S : Fma) .{i : isNeg S} {A B : Fma} (fs : All (λ C → S ⊢li C) (toTree A))
  → (c : CheckFocus {mkNeg S i} fs)
  → emb-f (∨r₁-li-neg S {B = B} fs c) ≗ ∨r₁ (∧r* _ (emb-li-fs fs))

emb∨r₁-li (` X) fs = emb∨r₁-li-neg _ fs (check-focus fs)
emb∨r₁-li (S ∧ S') fs = emb∨r₁-li-neg _ fs (check-focus fs)
emb∨r₁-li (S ∨ S') {` X} (leaf (∨l f f')) =
  ∨l (emb∨r₁-li S (leaf f)) (emb∨r₁-li S' (leaf f'))
  ∙ (~ ∨r₁∨l)
emb∨r₁-li (S ∨ S') {A ∧ A'} (node fs fs') =
  ∨l (emb∨r₁-li S _) (emb∨r₁-li S' _)
  ∙ (~ ∨r₁∨l)
  ∙ ∨r₁ ((~ ∧r∨l)
         ∙ ∧r ((~ ∧r*∨l _ _)
               ∙ ≡to≗ (cong (∧r* A) (trans (map2All-comp _ _)
                                    (trans (map2All-comp _ _)
                                    (trans (map2All-Δ _)
                                           (mapAll-eq1 (λ { (∨l f g) → refl }) fs))))))
              ((~ ∧r*∨l _ _)
               ∙ ≡to≗ (cong (∧r* A') (trans (map2All-comp _ _)
                                     (trans (map2All-comp _ _)
                                     (trans (map2All-Δ _)
                                            (mapAll-eq1 (λ { (∨l f g) → refl }) fs')))))))
emb∨r₁-li (S ∨ S') {A ∨ A'} (leaf (∨l f f')) = 
  ∨l (emb∨r₁-li S (leaf f)) (emb∨r₁-li S' (leaf f'))
  ∙ (~ ∨r₁∨l)

emb∨r₁-li-neg (` X) fs (caseok ok) = ∨r₁ (emb-ri-∧r*-ri _ fs)
emb∨r₁-li-neg (S ∧ S') fs (case1 (all∧l₁ gs refl refl)) =
  ∧l₁ (emb∨r₁-li S gs)
  ∙ (~ ∨r₁∧l₁)
  ∙ ∨r₁ (~ ∧r*∧l₁ _
         ∙ ≡to≗ (cong (∧r* _) (trans (mapAll-comp _)
                              (trans (sym (mapAll-comp _))
                                     (sym (mapAll-comp _))))))
emb∨r₁-li-neg (S ∧ S') fs (case2 (all∧l₂ gs refl refl)) = 
  ∧l₂ (emb∨r₁-li S' gs)
  ∙ (~ ∨r₁∧l₂)
  ∙ ∨r₁ (~ ∧r*∧l₂ _
         ∙ ≡to≗ (cong (∧r* _) (trans (mapAll-comp _)
                              (trans (sym (mapAll-comp _))
                                     (sym (mapAll-comp _))))))
emb∨r₁-li-neg (S ∧ S') fs (caseok ok) = ∨r₁ (emb-ri-∧r*-ri _ fs)

emb∨r₂-li : (S : Fma) {A B : Fma} (fs : All (λ C → S ⊢li C) (toTree B))
  → emb-li (∨r₂-li S {A = A} fs) ≗ ∨r₂ (∧r* _ (emb-li-fs fs))
emb∨r₂-li-neg : (S : Fma) .{i : isNeg S} {A B : Fma} (fs : All (λ C → S ⊢li C) (toTree B))
  → (c : CheckFocus {mkNeg S i} fs)
  → emb-f (∨r₂-li-neg S {A = A} fs c) ≗ ∨r₂ (∧r* _ (emb-li-fs fs))

emb∨r₂-li (` X) fs = emb∨r₂-li-neg _ fs (check-focus fs)
emb∨r₂-li (S ∧ S') fs = emb∨r₂-li-neg _ fs (check-focus fs)
emb∨r₂-li (S ∨ S') {B = ` X} (leaf (∨l f f')) =
  ∨l (emb∨r₂-li S (leaf f)) (emb∨r₂-li S' (leaf f'))
  ∙ (~ ∨r₂∨l)
emb∨r₂-li (S ∨ S') {B = B ∧ B'} (node fs fs') =
  ∨l (emb∨r₂-li S _) (emb∨r₂-li S' _)
  ∙ (~ ∨r₂∨l)
  ∙ ∨r₂ ((~ ∧r∨l)
         ∙ ∧r ((~ ∧r*∨l _ _)
               ∙ ≡to≗ (cong (∧r* B) (trans (map2All-comp _ _)
                                    (trans (map2All-comp _ _)
                                    (trans (map2All-Δ _)
                                           (mapAll-eq1 (λ { (∨l f g) → refl }) fs))))))
              ((~ ∧r*∨l _ _)
               ∙ ≡to≗ (cong (∧r* B') (trans (map2All-comp _ _)
                                     (trans (map2All-comp _ _)
                                     (trans (map2All-Δ _)
                                            (mapAll-eq1 (λ { (∨l f g) → refl }) fs')))))))
emb∨r₂-li (S ∨ S') {B = B ∨ B'} (leaf (∨l f f')) = 
  ∨l (emb∨r₂-li S (leaf f)) (emb∨r₂-li S' (leaf f'))
  ∙ (~ ∨r₂∨l)

emb∨r₂-li-neg (` X) fs (caseok ok) = ∨r₂ (emb-ri-∧r*-ri _ fs)
emb∨r₂-li-neg (S ∧ S') fs (case1 (all∧l₁ gs refl refl)) =
  ∧l₁ (emb∨r₂-li S gs)
  ∙ (~ ∨r₂∧l₁)
  ∙ ∨r₂ (~ ∧r*∧l₁ _
         ∙ ≡to≗ (cong (∧r* _) (trans (mapAll-comp _)
                              (trans (sym (mapAll-comp _))
                                     (sym (mapAll-comp _))))))
emb∨r₂-li-neg (S ∧ S') fs (case2 (all∧l₂ gs refl refl)) = 
  ∧l₂ (emb∨r₂-li S' gs)
  ∙ (~ ∨r₂∧l₂)
  ∙ ∨r₂ (~ ∧r*∧l₂ _
         ∙ ≡to≗ (cong (∧r* _) (trans (mapAll-comp _)
                              (trans (sym (mapAll-comp _))
                                     (sym (mapAll-comp _))))))
emb∨r₂-li-neg (S ∧ S') fs (caseok ok) = ∨r₂ (emb-ri-∧r*-ri _ fs)


emb∨r₁ : {S A B : Fma} (f : S ⊢ri A) → emb-ri (∨r₁-ri {B = B} f) ≗ ∨r₁ (emb-ri f)
emb∨r₁ f =
  emb∨r₁-li _ _
  ∙ ∨r₁ (~ (emb-ri-∧r*-ri _ _)
         ∙ ≡to≗ (cong emb-ri (∧r*∧r*-ri-inv f)))

emb∨r₂ : {S A B : Fma} (f : S ⊢ri B) → emb-ri (∨r₂-ri {A = A} f) ≗ ∨r₂ (emb-ri f)
emb∨r₂ f =
  emb∨r₂-li _ _
  ∙ ∨r₂ (~ (emb-ri-∧r*-ri _ _)
         ∙ ≡to≗ (cong emb-ri (∧r*∧r*-ri-inv f)))

emb∨l :  {A B C : Fma}
  → (f : A ⊢ri C) (g :  B ⊢ri C)
  → emb-ri (∨l-ri f g) ≗ ∨l (emb-ri f) (emb-ri g)
emb∨l (∧r f f₁) (∧r g g₁) = ∧r (emb∨l f g) (emb∨l f₁ g₁) ∙ ∧r∨l
emb∨l (li2ri f) (li2ri g) = refl

emb∧l₁ :  {A B C : Fma}
  → (f : A ⊢ri C)
  → emb-ri (∧l₁-ri {B = B} f) ≗ ∧l₁ (emb-ri f)
emb∧l₁ (∧r f g) = ∧r (emb∧l₁ f) (emb∧l₁ g) ∙ (∧r∧l₁ ∙ ∧l₁ refl)
emb∧l₁ (li2ri f) = refl

emb∧l₂ :  {A B C : Fma}
  → (f : B ⊢ri C)
  → emb-ri (∧l₂-ri {A = A} f) ≗ ∧l₂ (emb-ri f)
emb∧l₂ (∧r f g) = ∧r (emb∧l₂ f) (emb∧l₂ g) ∙ (∧r∧l₂ ∙ ∧l₂ refl)
emb∧l₂ (li2ri f) = refl

embax : {D : Fma}
  → emb-ri (ax-ri D) ≗ ax
embax {` x} = refl
embax {D1 ∧ D2} =
  ∧r (emb∧l₁ (ax-ri D1)) (emb∧l₂ (ax-ri D2))
  ∙ ∧r (∧l₁ (embax {D = D1})) (∧l₂ (embax {D = D2}))
  ∙ (~ ax∧)
embax {D1 ∨ D2} =
  emb∨l (∨r₁-ri (ax-ri D1)) (∨r₂-ri (ax-ri D2))
  ∙ ∨l (emb∨r₁ (ax-ri D1)) (emb∨r₂ (ax-ri D2))
  ∙ ∨l (∨r₁ embax) (∨r₂ embax)
  ∙ (~ ax∨)

-- embfocus, every derivation in SeqCalc is ≗-to the its normal form,
-- i.e. emb-ri (focus f) ≗ f
embfocus : {S : Fma}  {C : Fma}
  → (f : S ⊢ C)
  → emb-ri (focus f) ≗ f
embfocus ax = embax
embfocus (∧r f g) = ∧r (embfocus f) (embfocus g)
embfocus (∧l₁ f) = emb∧l₁ (focus f) ∙ ∧l₁ (embfocus f)
embfocus (∧l₂ f) = emb∧l₂ (focus f) ∙ ∧l₂ (embfocus f)
embfocus (∨r₁ f) = emb∨r₁ (focus f) ∙ ∨r₁ (embfocus f)
embfocus (∨r₂ f) = emb∨r₂ (focus f) ∙ ∨r₂ (embfocus f)
embfocus (∨l f g) = emb∨l (focus f) (focus g) ∙ ∨l (embfocus f) (embfocus g)        
