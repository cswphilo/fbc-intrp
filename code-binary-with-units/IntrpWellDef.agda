module IntrpWellDef where

open import Data.Product
open import Data.Sum using (inj₁; inj₂) renaming ([_,_]′ to elim⊎)
open import Formulae
open import SeqCalc
open import Cut
open import CutProperties
open import CutIntrp
open import Mip
open import IntrpTriples

∧l₁~' : ∀ {A B C} → MIP A C → MIP (A ∧ B) C
∧l₁~' {B = B} (intrp D g h vg vh) = intrp D (∧l₁ {B = B} g) h (λ m → inj₁ (vg m)) vh

∧l₁~ : ∀ {A B C} {n n' : MIP A C}
  → n ~ n'
  → ∧l₁~' {B = B} n ~ ∧l₁~' n'
∧l₁~ refl = refl
∧l₁~ (↝∷ {n = intrp D g h vg vh} (t , eqg , eqh) p) =
  ↝∷ (t , (cut∧l₁≗ g t ∙ ∧l₁ eqg) , eqh) (∧l₁~ p)
∧l₁~ (↜∷ {n' = intrp D g h vg vh} (t , eqg , eqh) p) =
  ↜∷ (t , (cut∧l₁≗ g t ∙ ∧l₁ eqg) , eqh) (∧l₁~ p)

∧l₂~' : ∀ {A B C} → MIP B C → MIP (A ∧ B) C
∧l₂~' {A = A} (intrp D g h vg vh) = intrp D (∧l₂ {A = A} g) h (λ m → inj₂ (vg m)) vh

∧l₂~ : ∀ {A B C} {n n' : MIP B C}
  → n ~ n'
  → ∧l₂~' {A = A} n ~ ∧l₂~' n'
∧l₂~ refl = refl
∧l₂~ (↝∷ {n = intrp D g h vg vh} (t , eqg , eqh) p) =
  ↝∷ (t , (cut∧l₂≗ g t ∙ ∧l₂ eqg) , eqh) (∧l₂~ p)
∧l₂~ (↜∷ {n' = intrp D g h vg vh} (t , eqg , eqh) p) =
  ↜∷ (t , (cut∧l₂≗ g t ∙ ∧l₂ eqg) , eqh) (∧l₂~ p)

∨r₁~' : ∀ {S A B} → MIP S A → MIP S (A ∨ B)
∨r₁~' {B = B} (intrp D g h vg vh) = intrp D g (∨r₁ {B = B} h) vg (λ m → inj₁ (vh m))

∨r₁~ : ∀ {S A B} {n n' : MIP S A}
  → n ~ n'
  → ∨r₁~' {B = B} n ~ ∨r₁~' n'
∨r₁~ refl = refl
∨r₁~ (↝∷ (t , eqg , eqh) p) =
  ↝∷ (t , eqg , ∨r₁ eqh) (∨r₁~ p)
∨r₁~ (↜∷ (t , eqg , eqh) p) =
  ↜∷ (t , eqg , ∨r₁ eqh) (∨r₁~ p)

∨r₂~' : ∀ {S A B} → MIP S B → MIP S (A ∨ B)
∨r₂~' {A = A} (intrp D g h vg vh) = intrp D g (∨r₂ {A = A} h) vg (λ m → inj₂ (vh m))

∨r₂~ : ∀ {S A B} {n n' : MIP S B}
  → n ~ n'
  → ∨r₂~' {A = A} n ~ ∨r₂~' n'
∨r₂~ refl = refl
∨r₂~ (↝∷ (t , eqg , eqh) p) =
  ↝∷ (t , eqg , ∨r₂ eqh) (∨r₂~ p)
∨r₂~ (↜∷ (t , eqg , eqh) p) =
  ↜∷ (t , eqg , ∨r₂ eqh) (∨r₂~ p)

∧r~' : ∀ {S A B} → MIP S A → MIP S B → MIP S (A ∧ B)
∧r~' (intrp D g h vg vh) (intrp D' g' h' vg' vh') =
  intrp (D ∧ D') (∧r g g') (∧r (∧l₁ h) (∧l₂ h'))
    (λ m → elim⊎ vg vg' m)
    (λ m → elim⊎ (λ p → inj₁ (vh p)) (λ p → inj₂ (vh' p)) m)

∧r~ : ∀ {S A B}
  {n n' : MIP S A} {m m' : MIP S B}
  → n ~ n' → m ~ m'
  → ∧r~' n m ~ ∧r~' n' m'
∧r~ refl refl = refl
∧r~ {n = intrp D g h vg vh}
  refl
  (↝∷ {n = intrp E k l vk vl} {n' = intrp E' k' l' vk' vl'}
    (t , eqg , eqh) p) =
  ↝∷
    ( ∧r (∧l₁ ax) (∧l₂ t)
    , ∧r (cutaxA-right g) eqg
    , ∧r
        (~ (cut∧l₁≗ ax h ∙ ∧l₁ (cutaxA-left h)))
        (∧l₂ eqh ∙ (~ cut∧l₂≗ t l'))
    )
    (∧r~ refl p)
∧r~ {n = intrp D g h vg vh}
  refl
  (↜∷ {n = intrp E' k' l' vk' vl'} {n' = intrp E k l vk vl}
    (t , eqg , eqh) p) =
  ↜∷
    ( ∧r (∧l₁ ax) (∧l₂ t)
    , ∧r (cutaxA-right g) eqg
    , ∧r
        (~ (cut∧l₁≗ ax h ∙ ∧l₁ (cutaxA-left h)))
        (∧l₂ eqh ∙ (~ cut∧l₂≗ t l'))
    )
    (∧r~ refl p)
∧r~ {m = intrp E k l vk vl}
  (↝∷ {n = intrp D g h vg vh} {n' = intrp D' g' h' vg' vh'}
    (t , eqg , eqh) p)
  q =
  ↝∷
    ( ∧r (∧l₁ t) (∧l₂ ax)
    , ∧r eqg (cutaxA-right k)
    , ∧r
        (∧l₁ eqh ∙ (~ cut∧l₁≗ t h'))
        (~ (cut∧l₂≗ ax l ∙ ∧l₂ (cutaxA-left l)))
    )
    (∧r~ p q)
∧r~ {m = intrp E k l vk vl}
  (↜∷ {n = intrp D' g' h' vg' vh'} {n' = intrp D g h vg vh}
    (t , eqg , eqh) p)
  q =
  ↜∷
    ( ∧r (∧l₁ t) (∧l₂ ax)
    , ∧r eqg (cutaxA-right k)
    , ∧r
        (∧l₁ eqh ∙ (~ cut∧l₁≗ t h'))
        (~ (cut∧l₂≗ ax l ∙ ∧l₂ (cutaxA-left l)))
    )
    (∧r~ p q)

∨l~' : ∀ {A B C} → MIP A C → MIP B C → MIP (A ∨ B) C
∨l~' (intrp D g h vg vh) (intrp D' g' h' vg' vh') =
  intrp (D ∨ D') (∨l (∨r₁ g) (∨r₂ g')) (∨l h h')
    (λ m → elim⊎ (λ p → inj₁ (vg p)) (λ p → inj₂ (vg' p)) m)
    (λ m → elim⊎ vh vh' m)

∨l~ : ∀ {A B C}
  {n n' : MIP A C} {m m' : MIP B C}
  → n ~ n' → m ~ m'
  → ∨l~' n m ~ ∨l~' n' m'
∨l~ refl refl = refl
∨l~ {n = intrp D g h vg vh}
  refl
  (↝∷ {n = intrp E k l vk vl} {n' = intrp E' k' l' vk' vl'}
    (t , eqg , eqh) p) =
  ↝∷
    ( ∨l (∨r₁ ax) (∨r₂ t)
    , ∨l (∨r₁ (cutaxA-right g)) (∨r₂ eqg)
    , ∨l (~ cutaxA-left h) eqh
    )
    (∨l~ refl p)
∨l~ {n = intrp D g h vg vh}
  refl
  (↜∷ {n = intrp E' k' l' vk' vl'} {n' = intrp E k l vk vl}
    (t , eqg , eqh) p) =
  ↜∷
    ( ∨l (∨r₁ ax) (∨r₂ t)
    , ∨l (∨r₁ (cutaxA-right g)) (∨r₂ eqg)
    , ∨l (~ cutaxA-left h) eqh
    )
    (∨l~ refl p)
∨l~ {m = intrp E k l vk vl}
  (↝∷ {n = intrp D g h vg vh} {n' = intrp D' g' h' vg' vh'}
    (t , eqg , eqh) p)
  q =
  ↝∷
    ( ∨l (∨r₁ t) (∨r₂ ax)
    , ∨l (∨r₁ eqg) (∨r₂ (cutaxA-right k))
    , ∨l eqh (~ cutaxA-left l)
    )
    (∨l~ p q)
∨l~ {m = intrp E k l vk vl}
  (↜∷ {n = intrp D' g' h' vg' vh'} {n' = intrp D g h vg vh}
    (t , eqg , eqh) p)
  q =
  ↜∷
    ( ∨l (∨r₁ t) (∨r₂ ax)
    , ∨l (∨r₁ eqg) (∨r₂ (cutaxA-right k))
    , ∨l eqh (~ cutaxA-left l)
    )
    (∨l~ p q)

mip≗ : ∀ {A C} {f f' : A ⊢ C}
  → f ≗ f'
  → mip f ~ mip f'
mip≗ refl = refl
mip≗ (~ p) = ~-sym (mip≗ p)
mip≗ (p ∙ p') = ~-trans (mip≗ p) (mip≗ p')
mip≗ (∧r p p') = ∧r~ (mip≗ p) (mip≗ p')
mip≗ (∧l₁ p) = ∧l₁~ (mip≗ p)
mip≗ (∧l₂ p) = ∧l₂~ (mip≗ p)
mip≗ (∨r₁ p) = ∨r₁~ (mip≗ p)
mip≗ (∨r₂ p) = ∨r₂~ (mip≗ p)
mip≗ (∨l p p') = ∨l~ (mip≗ p) (mip≗ p')
mip≗ ax∧ = ~-trans (g~ {vg' = λ m → m} {vh' = λ m → m} ax∧) (h~ ax∧)
mip≗ ax∨ = ~-trans (g~ {vg' = λ m → m} {vh' = λ m → m} ax∨) (h~ ax∨)
mip≗ ∧r∧l₁ = g~ ∧r∧l₁
mip≗ ∧r∧l₂ = g~ ∧r∧l₂
mip≗ (∧r∨l {f = f} {f' = f'} {g = g} {g' = g'}) =
  let intrp D₁ g₁ h₁ vg₁ vh₁ = mip f
      intrp D₂ g₂ h₂ vg₂ vh₂ = mip f'
      intrp D₃ g₃ h₃ vg₃ vh₃ = mip g
      intrp D₄ g₄ h₄ vg₄ vh₄ = mip g'
  in ↜∷ (
        ∨l (∧r (∨r₁ (∧l₁ ax)) (∨r₁ (∧l₂ ax)))
           (∧r (∨r₂ (∧l₁ ax)) (∨r₂ (∧l₂ ax))) , 
        (~ ∧r∨l) ,
        (~ ∧r∨l) ∙ 
        ∧r (∨l ((~ ∧l₁ (cutaxA-left h₁)) ∙ (~ cut∧l₁≗ ax h₁)) 
               ((~ ∧l₁ (cutaxA-left h₃)) ∙ (~ cut∧l₁≗ ax h₃))) 
           (∨l ((~ ∧l₂ (cutaxA-left h₂)) ∙ (~ cut∧l₂≗ ax h₂))
               ((~ ∧l₂ (cutaxA-left h₄)) ∙ (~ cut∧l₂≗ ax h₄)))) refl
mip≗ ∨r₁∧l₁ = refl
mip≗ ∨r₁∧l₂ = refl
mip≗ ∨r₁∨l = h~ ∨r₁∨l
mip≗ ∨r₂∧l₁ = refl
mip≗ ∨r₂∧l₂ = refl
mip≗ ∨r₂∨l = h~ ∨r₂∨l
mip≗ (⊤rf {f = f}) =
  let intrp D g h vg vh = mip f
  in ↝∷ (⊤r , refl , ⊤rf) refl
mip≗ (⊥lf {f = f}) = 
  let intrp D g h vg vh = mip f
  in ↜∷ (g , cutaxA-left g , (~ ⊥lf)) refl
