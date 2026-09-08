module IntrpCut where

open import Data.Product
open import Formulae 
open import SeqCalc
open import Cut
open import CutProperties
open import Mip
open import CutIntrp
open import IntrpTriples
open import IntrpWellDef

postulate cut-cong₁ : ∀ {A B C} → {f f' : A ⊢ B} (g : B ⊢ C) → (p : f ≗ f') → cut f g ≗ cut f' g
          cut-cong₂ : ∀ {A B C} → {g g' : B ⊢ C} (f : A ⊢ B) → (p : g ≗ g') → cut f g ≗ cut f g'

cut-mip-left : ∀ {A B C}
  → (f : A ⊢ B) (g : B ⊢ C)
  → let intrp D l k = mip f
    in cut l (cut k g) ≗ cut f g
cut-mip-left f g = 
  let intrp D l k = mip f
  in (~ cut-assoc l k g) ∙ cut-cong₁ g (cut-intrp f)
-- cut-mip-left f ax = cut-intrp f
-- cut-mip-left f ⊤r = refl
-- cut-mip-left ax ⊥l = refl
-- cut-mip-left ⊥l ⊥l = refl
-- cut-mip-left (∧l₁ f) ⊥l =
--   cut∧l₁≗ (mip f .MIP.g) (cut (mip f .MIP.h) ⊥l)
--     ∙ ∧l₁ (cut-mip-left f ⊥l)
-- cut-mip-left (∧l₂ f) ⊥l =
--   cut∧l₂≗ (mip f .MIP.g) (cut (mip f .MIP.h) ⊥l)
--     ∙ ∧l₂ (cut-mip-left f ⊥l)
-- cut-mip-left (∨l f f₁) ⊥l =
--   ∨l (cut-mip-left f ⊥l) (cut-mip-left f₁ ⊥l)
-- cut-mip-left f (∧r g g₁) =
--   ∧r (cut-mip-left f g) (cut-mip-left f g₁)
-- cut-mip-left ax (∧l₁ g) = refl
-- cut-mip-left ⊥l (∧l₁ g) = refl
-- cut-mip-left (∧r f f₁) (∧l₁ g) =
--   (~ cut-assoc (mip (∧r f f₁) .MIP.g)
--        (∧l₁ (mip f .MIP.h)) g)
--     ∙ cut-assoc (mip f .MIP.g) (mip f .MIP.h) g
--     ∙ cut-mip-left f g
-- cut-mip-left (∧l₁ f) (∧l₁ g) =
--   cut∧l₁≗ (mip f .MIP.g) (cut (mip f .MIP.h) (∧l₁ g))
--     ∙ ∧l₁ (cut-mip-left f (∧l₁ g))
-- cut-mip-left (∧l₂ f) (∧l₁ g) =
--   cut∧l₂≗ (mip f .MIP.g) (cut (mip f .MIP.h) (∧l₁ g))
--     ∙ ∧l₂ (cut-mip-left f (∧l₁ g))
-- cut-mip-left (∨l f f₁) (∧l₁ g) =
--   ∨l (cut-mip-left f (∧l₁ g)) (cut-mip-left f₁ (∧l₁ g))
-- cut-mip-left ax (∧l₂ g) = refl
-- cut-mip-left ⊥l (∧l₂ g) = refl
-- cut-mip-left (∧r f f₁) (∧l₂ g) =
--   (~ cut-assoc (mip (∧r f f₁) .MIP.g)
--        (∧l₂ (mip f₁ .MIP.h)) g)
--     ∙ cut-assoc (mip f₁ .MIP.g) (mip f₁ .MIP.h) g
--     ∙ cut-mip-left f₁ g
-- cut-mip-left (∧l₁ f) (∧l₂ g) =
--   cut∧l₁≗ (mip f .MIP.g) (cut (mip f .MIP.h) (∧l₂ g))
--     ∙ ∧l₁ (cut-mip-left f (∧l₂ g))
-- cut-mip-left (∧l₂ f) (∧l₂ g) =
--   cut∧l₂≗ (mip f .MIP.g) (cut (mip f .MIP.h) (∧l₂ g))
--     ∙ ∧l₂ (cut-mip-left f (∧l₂ g))
-- cut-mip-left (∨l f f₁) (∧l₂ g) =
--   ∨l (cut-mip-left f (∧l₂ g)) (cut-mip-left f₁ (∧l₂ g))
-- cut-mip-left f (∨r₁ g) = ∨r₁ (cut-mip-left f g)
-- cut-mip-left f (∨r₂ g) = ∨r₂ (cut-mip-left f g)
-- cut-mip-left ax (∨l g g₁) = refl
-- cut-mip-left ⊥l (∨l g g₁) = refl
-- cut-mip-left (∧l₁ f) (∨l g g₁) =
--   cut∧l₁≗ (mip f .MIP.g) (cut (mip f .MIP.h) (∨l g g₁))
--     ∙ ∧l₁ (cut-mip-left f (∨l g g₁))
-- cut-mip-left (∧l₂ f) (∨l g g₁) =
--   cut∧l₂≗ (mip f .MIP.g) (cut (mip f .MIP.h) (∨l g g₁))
--     ∙ ∧l₂ (cut-mip-left f (∨l g g₁))
-- cut-mip-left (∨r₁ f) (∨l g g₁) = cut-mip-left f g
-- cut-mip-left (∨r₂ f) (∨l g g₁) = cut-mip-left f g₁
-- cut-mip-left (∨l f f₁) (∨l g g₁) =
--   ∨l (cut-mip-left f (∨l g g₁)) (cut-mip-left f₁ (∨l g g₁))

cut-mip-right : ∀ {A B C}
  → (f : A ⊢ B) (g : B ⊢ C)
  → let intrp D l k = mip g
    in cut (cut f l) k ≗ cut f g
cut-mip-right f g =
  let intrp D l k = mip g
  in cut-assoc f l k ∙ cut-cong₂ f (cut-intrp g)
-- cut-mip-right f ax = refl
-- cut-mip-right f ⊤r = refl
-- cut-mip-right f ⊥l = refl
-- cut-mip-right f (∧r g g₁) =
--   ∧r (cut-mip-right f g) (cut-mip-right f g₁)
-- cut-mip-right ax (∧l₁ g) = cut-intrp (∧l₁ g)
-- cut-mip-right ⊥l (∧l₁ g) = ⊥lf ∙ (~ ⊥lf)
-- cut-mip-right (∧r f f₁) (∧l₁ g) = cut-mip-right f g
-- cut-mip-right (∧l₁ f) (∧l₁ g) =
--   cut∧l₁≗ (cut f (∧l₁ (mip g .MIP.g))) (mip g .MIP.h)
--     ∙ ∧l₁ (cut-mip-right f (∧l₁ g))
-- cut-mip-right (∧l₂ f) (∧l₁ g) =
--   cut∧l₂≗ (cut f (∧l₁ (mip g .MIP.g))) (mip g .MIP.h)
--     ∙ ∧l₂ (cut-mip-right f (∧l₁ g))
-- cut-mip-right (∨l f f₁) (∧l₁ g) =
--   cut∨l≗ (cut f (∧l₁ (mip g .MIP.g)))
--           (cut f₁ (∧l₁ (mip g .MIP.g)))
--           (mip g .MIP.h)
--     ∙ ∨l (cut-mip-right f (∧l₁ g))
--          (cut-mip-right f₁ (∧l₁ g))
-- cut-mip-right ax (∧l₂ g) = cut-intrp (∧l₂ g)
-- cut-mip-right ⊥l (∧l₂ g) = ⊥lf ∙ (~ ⊥lf)
-- cut-mip-right (∧r f f₁) (∧l₂ g) = cut-mip-right f₁ g
-- cut-mip-right (∧l₁ f) (∧l₂ g) =
--   cut∧l₁≗ (cut f (∧l₂ (mip g .MIP.g))) (mip g .MIP.h)
--     ∙ ∧l₁ (cut-mip-right f (∧l₂ g))
-- cut-mip-right (∧l₂ f) (∧l₂ g) =
--   cut∧l₂≗ (cut f (∧l₂ (mip g .MIP.g))) (mip g .MIP.h)
--     ∙ ∧l₂ (cut-mip-right f (∧l₂ g))
-- cut-mip-right (∨l f f₁) (∧l₂ g) =
--   cut∨l≗ (cut f (∧l₂ (mip g .MIP.g)))
--           (cut f₁ (∧l₂ (mip g .MIP.g)))
--           (mip g .MIP.h)
--     ∙ ∨l (cut-mip-right f (∧l₂ g))
--          (cut-mip-right f₁ (∧l₂ g))
-- cut-mip-right f (∨r₁ g) = ∨r₁ (cut-mip-right f g)
-- cut-mip-right f (∨r₂ g) = ∨r₂ (cut-mip-right f g)
-- cut-mip-right ax (∨l g g₁) = cut-intrp (∨l g g₁)
-- cut-mip-right ⊥l (∨l g g₁) = ⊥lf ∙ (~ ⊥lf)
-- cut-mip-right (∧l₁ f) (∨l g g₁) =
--   cut∧l₁≗ (cut f (mip (∨l g g₁) .MIP.g))
--            (mip (∨l g g₁) .MIP.h)
--     ∙ ∧l₁ (cut-mip-right f (∨l g g₁))
-- cut-mip-right (∧l₂ f) (∨l g g₁) =
--   cut∧l₂≗ (cut f (mip (∨l g g₁) .MIP.g))
--            (mip (∨l g g₁) .MIP.h)
--     ∙ ∧l₂ (cut-mip-right f (∨l g g₁))
-- cut-mip-right (∨r₁ f) (∨l g g₁) = cut-mip-right f g
-- cut-mip-right (∨r₂ f) (∨l g g₁) = cut-mip-right f g₁
-- cut-mip-right (∨l f f₁) (∨l g g₁) =
--   ∨l (cut-mip-right f (∨l g g₁))
--      (cut-mip-right f₁ (∨l g g₁))

intrp-cut-witness : ∀ {A C}
  → (n : MIP A C)
  → Σ (A ⊢ C) λ f → (f ≗ cut (n .MIP.g) (n .MIP.h)) × (n ~ mip f)
intrp-cut-witness (intrp D h ax) =
  let intrp E l k = mip h
  in h , refl ,
     ↜∷ {n = intrp D h ax} {n' = intrp E l k}
       (k , cut-intrp h , refl) refl
intrp-cut-witness (intrp D h ⊤r) =
  ⊤r , refl , ↝∷ (⊤r , refl , refl) refl
intrp-cut-witness (intrp ⊥ ax ⊥l) = ⊥l , refl , refl
intrp-cut-witness (intrp ⊥ ⊥l ⊥l) = ⊥l , refl , g~ (~ ⊥lf)
intrp-cut-witness (intrp ⊥ (∧l₁ h) ⊥l) =
  let f , eq , p = intrp-cut-witness (intrp ⊥ h ⊥l)
  in ∧l₁ f , ∧l₁ eq , ∧l₁~ p
intrp-cut-witness (intrp ⊥ (∧l₂ h) ⊥l) =
  let f , eq , p = intrp-cut-witness (intrp ⊥ h ⊥l)
  in ∧l₂ f , ∧l₂ eq , ∧l₂~ p
intrp-cut-witness (intrp ⊥ (∨l h h₁) ⊥l) =
  let f , eq , p = intrp-cut-witness (intrp ⊥ h ⊥l)
      f₁ , eq₁ , p₁ = intrp-cut-witness (intrp ⊥ h₁ ⊥l)
  in ∨l f f₁ , ∨l eq eq₁ ,
     ↜∷ {n' = ∨l~' (intrp ⊥ h ⊥l) (intrp ⊥ h₁ ⊥l)}
       (∨l ax ax , refl , refl) (∨l~ p p₁)

intrp-cut-witness (intrp D h (∧r g g₁)) =
  let intrp E l k = mip h
      intrp F n m = mip (cut k g)
      intrp F₁ n₁ m₁ = mip (cut k g₁)
      f , eq , p = intrp-cut-witness (intrp F (cut l n) m)
      f₁ , eq₁ , p₁ = intrp-cut-witness (intrp F₁ (cut l n₁) m₁)
  in ∧r f f₁
   , ∧r
       (eq ∙ cut-mip-right l (cut k g) ∙ cut-mip-left h g)
       (eq₁ ∙ cut-mip-right l (cut k g₁) ∙ cut-mip-left h g₁)
   , ↜∷ {n' = intrp E l (cut k (∧r g g₁))}
       (k , cut-intrp h , refl)
       (↝∷
         {n' = ∧r~' (intrp E l (cut k g)) (intrp E l (cut k g₁))}
         ( ∧r ax ax
         , refl
         , ∧r (~ cutaxA-left (cut k g)) (~ cutaxA-left (cut k g₁))
         )
         (∧r~
           (↝∷
             {n' = intrp F (cut l n) m}
             (n , refl , ~ cut-intrp (cut k g))
             p)
           (↝∷
             {n' = intrp F₁ (cut l n₁) m₁}
             (n₁ , refl , ~ cut-intrp (cut k g₁))
             p₁)))

{-
Previous conjunction-right proof:

intrp-cut-witness (intrp D h (∧r g g₁)) =
  let intrp E l k = mip h
      f , eq , p = intrp-cut-witness (intrp E l (cut k g))
      f₁ , eq₁ , p₁ = intrp-cut-witness (intrp E l (cut k g₁))
  in ∧r f f₁
   , ∧r (eq ∙ cut-mip-left h g) (eq₁ ∙ cut-mip-left h g₁)
   , ↜∷ {n' = intrp E l (cut k (∧r g g₁))}
       (k , cut-intrp h , refl)
       (↝∷
         {n' = ∧r~' (intrp E l (cut k g)) (intrp E l (cut k g₁))}
         ( ∧r ax ax
         , refl
         , ∧r (~ cutaxA-left (cut k g)) (~ cutaxA-left (cut k g₁))
         )
         (∧r~ p p₁))

This proof type-checks, but its recursive calls do not necessarily satisfy
the variable condition.  The formula E is suitable between A and the whole
target B ∧ C.  The recursive calls change that target to B and C separately.
A variable of E may occur only in C, so it is then absent from B; or it may
occur only in B, so it is absent from C.  The revised proof first applies mip
to cut k g and cut k g₁, obtaining F and F₁ for the separate targets.

For example, take

  A = D = (` X ∧ ` Y),  B = ` X,  C = ` Y,
  h = ax,  g = ∧l₁ ax,  g₁ = ∧l₂ ax.

Then mip h has middle formula E = ` X ∧ ` Y.  For the whole target
` X ∧ ` Y this is valid.  In the first recursive call the target is only
` X, so ` Y is missing from the target.  In the second recursive call the
target is only ` Y, so ` X is missing from the target.
-}

intrp-cut-witness (intrp D ax (∧l₁ {B = B} g)) =
  let intrp E l k = mip g
  in ∧l₁ g , refl , ↝∷ (∧l₁ l , refl , ∧l₁ (~ cut-intrp g) ∙ (~ cut∧l₁≗ l k)) refl
  -- ∧l₁ g , refl ,
  --    ↝∷ {n' = intrp E l k}
  --      (l , ~ cut-intrp (∧l₁ g) , cutaxA-left l) refl
intrp-cut-witness (intrp D ⊥l (∧l₁ g)) =
  ⊥l , refl ,
  ↜∷ {n' = intrp ⊥ ax ⊥l} (⊥l , refl , refl) refl
intrp-cut-witness (intrp D (∧r h h₁) (∧l₁ g)) =
  let f , eq , p = intrp-cut-witness (intrp _ h g)
  in f , eq ,
     ↝∷ {n' = intrp _ h g}
       ( ∧l₁ ax
       , refl
       , ~ (cut∧l₁≗ ax g ∙ ∧l₁ (cutaxA-left g))
       ) p
intrp-cut-witness (intrp D (∧l₁ h) (∧l₁ g)) =
  let f , eq , p = intrp-cut-witness (intrp D h (∧l₁ g))
  in ∧l₁ f , ∧l₁ eq , ∧l₁~ p
intrp-cut-witness (intrp D (∧l₂ h) (∧l₁ g)) =
  let f , eq , p = intrp-cut-witness (intrp D h (∧l₁ g))
  in ∧l₂ f , ∧l₂ eq , ∧l₂~ p
intrp-cut-witness (intrp D (∨l h h₁) (∧l₁ g)) =
  let f , eq , p = intrp-cut-witness (intrp D h (∧l₁ g))
      f₁ , eq₁ , p₁ = intrp-cut-witness (intrp D h₁ (∧l₁ g))
  in ∨l f f₁ , ∨l eq eq₁ ,
     ↜∷ {n' = ∨l~' (intrp D h (∧l₁ g)) (intrp D h₁ (∧l₁ g))}
       (∨l ax ax , refl , refl) (∨l~ p p₁)
intrp-cut-witness (intrp D ax (∧l₂ g)) =
  let intrp E l k = mip (∧l₂ g)
  in ∧l₂ g , refl ,
     ↝∷ {n' = intrp E l k}
       (l , cutaxA-left l , ~ cut-intrp (∧l₂ g)) refl
intrp-cut-witness (intrp D ⊥l (∧l₂ g)) =
  ⊥l , refl ,
  ↜∷ {n' = intrp ⊥ ax ⊥l} (⊥l , refl , refl) refl
intrp-cut-witness (intrp D (∧r h h₁) (∧l₂ g)) =
  let f , eq , p = intrp-cut-witness (intrp _ h₁ g)
  in f , eq ,
     ↝∷ {n' = intrp _ h₁ g}
       ( ∧l₂ ax
       , refl
       , ~ (cut∧l₂≗ ax g ∙ ∧l₂ (cutaxA-left g))
       ) p
intrp-cut-witness (intrp D (∧l₁ h) (∧l₂ g)) =
  let f , eq , p = intrp-cut-witness (intrp D h (∧l₂ g))
  in ∧l₁ f , ∧l₁ eq , ∧l₁~ p
intrp-cut-witness (intrp D (∧l₂ h) (∧l₂ g)) =
  let f , eq , p = intrp-cut-witness (intrp D h (∧l₂ g))
  in ∧l₂ f , ∧l₂ eq , ∧l₂~ p
intrp-cut-witness (intrp D (∨l h h₁) (∧l₂ g)) =
  let f , eq , p = intrp-cut-witness (intrp D h (∧l₂ g))
      f₁ , eq₁ , p₁ = intrp-cut-witness (intrp D h₁ (∧l₂ g))
  in ∨l f f₁ , ∨l eq eq₁ ,
     ↜∷ {n' = ∨l~' (intrp D h (∧l₂ g)) (intrp D h₁ (∧l₂ g))}
       (∨l ax ax , refl , refl) (∨l~ p p₁)
intrp-cut-witness (intrp D h (∨r₁ g)) =
  let f , eq , p = intrp-cut-witness (intrp D h g)
  in ∨r₁ f , ∨r₁ eq , ∨r₁~ p
intrp-cut-witness (intrp D h (∨r₂ g)) =
  let f , eq , p = intrp-cut-witness (intrp D h g)
  in ∨r₂ f , ∨r₂ eq , ∨r₂~ p
intrp-cut-witness (intrp D ax (∨l g g₁)) =
  let intrp E l k = mip (∨l g g₁)
  in ∨l g g₁ , refl ,
     ↝∷ {n' = intrp E l k}
       (l , cutaxA-left l , ~ cut-intrp (∨l g g₁)) refl
intrp-cut-witness (intrp D ⊥l (∨l g g₁)) =
  ⊥l , refl ,
  ↜∷ {n' = intrp ⊥ ax ⊥l} (⊥l , refl , refl) refl
intrp-cut-witness (intrp D (∧l₁ h) (∨l g g₁)) =
  let f , eq , p = intrp-cut-witness (intrp D h (∨l g g₁))
  in ∧l₁ f , ∧l₁ eq , ∧l₁~ p
intrp-cut-witness (intrp D (∧l₂ h) (∨l g g₁)) =
  let f , eq , p = intrp-cut-witness (intrp D h (∨l g g₁))
  in ∧l₂ f , ∧l₂ eq , ∧l₂~ p
intrp-cut-witness (intrp D (∨r₁ h) (∨l g g₁)) =
  let f , eq , p = intrp-cut-witness (intrp _ h g)
  in f , eq ,
     ↜∷ {n' = intrp _ h g}
       (∨r₁ ax , refl , ~ cutaxA-left g) p
intrp-cut-witness (intrp D (∨r₂ h) (∨l g g₁)) =
  let f , eq , p = intrp-cut-witness (intrp _ h g₁)
  in f , eq ,
     ↜∷ {n' = intrp _ h g₁}
       (∨r₂ ax , refl , ~ cutaxA-left g₁) p

{-
Previous disjunction-left proof:

intrp-cut-witness (intrp D (∨l h h₁) (∨l g g₁)) =
  let intrp E l k = mip (∨l g g₁)
      f , eq , p = intrp-cut-witness (intrp E (cut h l) k)
      f₁ , eq₁ , p₁ = intrp-cut-witness (intrp E (cut h₁ l) k)
  in ∨l f f₁
   , ∨l (eq ∙ cut-mip-right h (∨l g g₁))
          (eq₁ ∙ cut-mip-right h₁ (∨l g g₁))
   , ↝∷ {n' = intrp E (cut (∨l h h₁) l) k}
       (l , refl , ~ cut-intrp (∨l g g₁))
       (↜∷
         {n' = ∨l~' (intrp E (cut h l) k) (intrp E (cut h₁ l) k)}
         (∨l ax ax , refl , refl)
         (∨l~ p p₁))

This proof has the dual problem.  The formula E is suitable between the whole
source A ∨ B and C.  The recursive calls change that source to A and B
separately.  A variable of E may occur only in B, so it is then absent from A;
or it may occur only in A, so it is absent from B.  The revised proof first
applies mip to cut h l and cut h₁ l, obtaining F and F₁ for the separate
sources.

For example, take

  A = ` X,  B = ` Y,  D = C = (` X ∨ ` Y),
  h = ∨r₁ ax,  h₁ = ∨r₂ ax,
  g = ∨r₁ ax,  g₁ = ∨r₂ ax.

Then mip (∨l g g₁) has middle formula E = ` X ∨ ` Y.  For the whole source
` X ∨ ` Y this is valid.  In the first recursive call the source is only
` X, so ` Y is missing from the source.  In the second recursive call the
source is only ` Y, so ` X is missing from the source.
-}

intrp-cut-witness (intrp D (∨l h h₁) (∨l g g₁)) =
  let intrp E l k = mip (∨l g g₁)
      intrp F n m = mip (cut h l)
      intrp F₁ n₁ m₁ = mip (cut h₁ l)
      f , eq , p = intrp-cut-witness (intrp F n (cut m k))
      f₁ , eq₁ , p₁ = intrp-cut-witness (intrp F₁ n₁ (cut m₁ k))
  in ∨l f f₁
   , ∨l
       (eq ∙ cut-mip-left (cut h l) k
           ∙ cut-mip-right h (∨l g g₁))
       (eq₁ ∙ cut-mip-left (cut h₁ l) k
            ∙ cut-mip-right h₁ (∨l g g₁))
   , ↝∷ {n' = intrp E (cut (∨l h h₁) l) k}
       (l , refl , ~ cut-intrp (∨l g g₁))
       (↜∷
         {n' = ∨l~' (intrp E (cut h l) k) (intrp E (cut h₁ l) k)}
         (∨l ax ax , refl , refl)
         (∨l~
           (↜∷
             {n' = intrp F n (cut m k)}
             (m , cut-intrp (cut h l) , refl)
             p)
           (↜∷
             {n' = intrp F₁ n₁ (cut m₁ k)}
             (m₁ , cut-intrp (cut h₁ l) , refl)
             p₁)))

intrp-cut : ∀ {A C}
  → (n : MIP A C)
  → n ~ mip (cut (n .MIP.g) (n .MIP.h))
intrp-cut n =
  let f , eq , p = intrp-cut-witness n
  in ~-trans p (mip≗ eq)
