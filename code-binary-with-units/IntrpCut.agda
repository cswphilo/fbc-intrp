module IntrpCut where

open import Data.Product
open import Data.Sum using (inj₁; inj₂)
open import Formulae 
open import SeqCalc
open import Cut
open import CutProperties
open import Mip
open import VarCondition
open import CutIntrp
open import IntrpTriples
open import IntrpWellDef

postulate cut-cong₁ : ∀ {A B C} → {f f' : A ⊢ B} (g : B ⊢ C) → (p : f ≗ f') → cut f g ≗ cut f' g
          cut-cong₂ : ∀ {A B C} → {g g' : B ⊢ C} (f : A ⊢ B) → (p : g ≗ g') → cut f g ≗ cut f g'

cut-mip-left : ∀ {A B C}
  → (f : A ⊢ B) (g : B ⊢ C)
  → let intrp D l k vl vk = mip f
    in cut l (cut k g) ≗ cut f g
cut-mip-left f g = 
  let intrp D l k vl vk = mip f
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
  → let intrp D l k vl vk = mip g
    in cut (cut f l) k ≗ cut f g
cut-mip-right f g =
  let intrp D l k vl vk = mip g
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

intrp-cut-witness' : ∀ {A C} (D : Fma)
  → (h : A ⊢ D) (g : D ⊢ C)
  → (vg : ∀ {X} → X ∈F D → X ∈F A)
  → (vh : ∀ {X} → X ∈F D → X ∈F C)
  → Σ (A ⊢ C) λ f → (f ≗ cut h g) × (intrp D h g vg vh ~ mip f)
intrp-cut-witness' D h ax vg vh =
  let intrp E l k vl vk = mip h
  in h , refl ,
     ↜∷ {n' = intrp E l k vl vk}
       (k , cut-intrp h , refl) refl
intrp-cut-witness' D h ⊤r vg vh =
  ⊤r , refl , ↝∷ (⊤r , refl , refl) refl
intrp-cut-witness' ⊥ ax ⊥l vg vh = ⊥l , refl , g~ refl
intrp-cut-witness' ⊥ ⊥l ⊥l vg vh = ⊥l , refl , g~ (~ ⊥lf)
intrp-cut-witness' ⊥ (∧l₁ h) ⊥l vg vh =
  let f , eq , p = intrp-cut-witness' ⊥ h ⊥l (λ ()) (λ ())
  in ∧l₁ f , ∧l₁ eq , ~-trans (g~ refl) (∧l₁~ p)
intrp-cut-witness' ⊥ (∧l₂ h) ⊥l vg vh =
  let f , eq , p = intrp-cut-witness' ⊥ h ⊥l (λ ()) (λ ())
  in ∧l₂ f , ∧l₂ eq , ~-trans (g~ refl) (∧l₂~ p)
intrp-cut-witness' ⊥ (∨l h h₁) ⊥l vg vh =
  let f , eq , p = intrp-cut-witness' ⊥ h ⊥l (λ ()) (λ ())
      f₁ , eq₁ , p₁ = intrp-cut-witness' ⊥ h₁ ⊥l (λ ()) (λ ())
  in ∨l f f₁ , ∨l eq eq₁ ,
     ↜∷ {n' = ∨l~' (intrp ⊥ h ⊥l (λ ()) (λ ())) (intrp ⊥ h₁ ⊥l (λ ()) (λ ()))}
       (∨l ax ax , refl , refl) (∨l~ p p₁)

intrp-cut-witness' D h (∧r g g₁) vg vh =
  let intrp E l k vl vk = mip h
      intrp F n m vn vm = mip (cut k g)
      intrp F₁ n₁ m₁ vn₁ vm₁ = mip (cut k g₁)
      f , eq , p = intrp-cut-witness' F (cut l n) m (λ q → vl (vn q)) vm
      f₁ , eq₁ , p₁ = intrp-cut-witness' F₁ (cut l n₁) m₁ (λ q → vl (vn₁ q)) vm₁
  in ∧r f f₁
   , ∧r
       (eq ∙ cut-mip-right l (cut k g) ∙ cut-mip-left h g)
       (eq₁ ∙ cut-mip-right l (cut k g₁) ∙ cut-mip-left h g₁)
   , ↜∷ {n' = intrp E l (cut k (∧r g g₁)) vl (λ q → vh (vk q))}
       (k , cut-intrp h , refl)
       (↝∷
         {n' = ∧r~' (intrp F (cut l n) m (λ q → vl (vn q)) vm)
                    (intrp F₁ (cut l n₁) m₁ (λ q → vl (vn₁ q)) vm₁)}
         ( ∧r n n₁
         , refl
         , ∧r (~ cut-intrp (cut k g)) (~ cut-intrp (cut k g₁))
         )
         (∧r~ p p₁))

intrp-cut-witness' D ax (∧l₁ {B = B} g) vg vh =
  let intrp E l k vl vk = mip g
  in ∧l₁ g , refl , ↝∷ (∧l₁ l , refl , ∧l₁ (~ cut-intrp g) ∙ (~ cut∧l₁≗ l k)) refl
intrp-cut-witness' D ⊥l (∧l₁ g) vg vh =
  ⊥l , refl ,
  ↜∷ {n' = intrp ⊥ ax ⊥l (λ ()) (λ ())} (⊥l , refl , refl) refl
intrp-cut-witness' D (∧r h h₁) (∧l₁ g) vg vh =
  let f , eq , p = intrp-cut-witness' _ h g (λ q → vg (inj₁ q)) (λ q → vh (inj₁ q))
  in f , eq ,
     ↝∷ {n' = intrp _ h g (λ q → vg (inj₁ q)) (λ q → vh (inj₁ q))}
       ( ∧l₁ ax
       , refl
       , ~ (cut∧l₁≗ ax g ∙ ∧l₁ (cutaxA-left g))
       ) p
intrp-cut-witness' D (∧l₁ h) (∧l₁ g) vg vh =
  let intrp E l k vl vk = mip h
      f , eq , p = intrp-cut-witness' E l (cut k (∧l₁ g)) vl (λ q → vh (vk q))
  in ∧l₁ f , ∧l₁ (eq ∙ cut-mip-left h (∧l₁ g)) ,
     ↜∷ {n' = ∧l₁~' (intrp E l (cut k (∧l₁ g)) vl (λ q → vh (vk q)))}
       (k , cut∧l₁≗ l k ∙ ∧l₁ (cut-intrp h) , refl) (∧l₁~ p)
intrp-cut-witness' D (∧l₂ h) (∧l₁ g) vg vh =
  let intrp E l k vl vk = mip h
      f , eq , p = intrp-cut-witness' E l (cut k (∧l₁ g)) vl (λ q → vh (vk q))
  in ∧l₂ f , ∧l₂ (eq ∙ cut-mip-left h (∧l₁ g)) ,
     ↜∷ {n' = ∧l₂~' (intrp E l (cut k (∧l₁ g)) vl (λ q → vh (vk q)))}
       (k , cut∧l₂≗ l k ∙ ∧l₂ (cut-intrp h) , refl) (∧l₂~ p)
intrp-cut-witness' D (∨l h h₁) (∧l₁ g) vg vh =
  let intrp E l k vl vk = mip h
      intrp E₁ l₁ k₁ vl₁ vk₁ = mip h₁
      f , eq , p = intrp-cut-witness' E l (cut k (∧l₁ g)) vl (λ q → vh (vk q))
      f₁ , eq₁ , p₁ = intrp-cut-witness' E₁ l₁ (cut k₁ (∧l₁ g)) vl₁ (λ q → vh (vk₁ q))
  in ∨l f f₁ , ∨l (eq ∙ cut-mip-left h (∧l₁ g)) (eq₁ ∙ cut-mip-left h₁ (∧l₁ g)) ,
     ↜∷ {n' = ∨l~' (intrp E l (cut k (∧l₁ g)) vl (λ q → vh (vk q)))
                    (intrp E₁ l₁ (cut k₁ (∧l₁ g)) vl₁ (λ q → vh (vk₁ q)))}
       (∨l k k₁ , ∨l (cut-intrp h) (cut-intrp h₁) , ~ cut∨l≗ k k₁ (∧l₁ g)) (∨l~ p p₁)
intrp-cut-witness' D ax (∧l₂ g) vg vh =
  let intrp E l k vl vk = mip (∧l₂ g)
  in ∧l₂ g , refl ,
     ↝∷ {n' = intrp E l k vl vk}
       (l , cutaxA-left l , ~ cut-intrp (∧l₂ g)) refl
intrp-cut-witness' D ⊥l (∧l₂ g) vg vh =
  ⊥l , refl ,
  ↜∷ {n' = intrp ⊥ ax ⊥l (λ ()) (λ ())} (⊥l , refl , refl) refl
intrp-cut-witness' D (∧r h h₁) (∧l₂ g) vg vh =
  let f , eq , p = intrp-cut-witness' _ h₁ g (λ q → vg (inj₂ q)) (λ q → vh (inj₂ q))
  in f , eq ,
     ↝∷ {n' = intrp _ h₁ g (λ q → vg (inj₂ q)) (λ q → vh (inj₂ q))}
       ( ∧l₂ ax
       , refl
       , ~ (cut∧l₂≗ ax g ∙ ∧l₂ (cutaxA-left g))
       ) p
intrp-cut-witness' D (∧l₁ h) (∧l₂ g) vg vh =
  let intrp E l k vl vk = mip h
      f , eq , p = intrp-cut-witness' E l (cut k (∧l₂ g)) vl (λ q → vh (vk q))
  in ∧l₁ f , ∧l₁ (eq ∙ cut-mip-left h (∧l₂ g)) ,
     ↜∷ {n' = ∧l₁~' (intrp E l (cut k (∧l₂ g)) vl (λ q → vh (vk q)))}
       (k , cut∧l₁≗ l k ∙ ∧l₁ (cut-intrp h) , refl) (∧l₁~ p)
intrp-cut-witness' D (∧l₂ h) (∧l₂ g) vg vh =
  let intrp E l k vl vk = mip h
      f , eq , p = intrp-cut-witness' E l (cut k (∧l₂ g)) vl (λ q → vh (vk q))
  in ∧l₂ f , ∧l₂ (eq ∙ cut-mip-left h (∧l₂ g)) ,
     ↜∷ {n' = ∧l₂~' (intrp E l (cut k (∧l₂ g)) vl (λ q → vh (vk q)))}
       (k , cut∧l₂≗ l k ∙ ∧l₂ (cut-intrp h) , refl) (∧l₂~ p)
intrp-cut-witness' D (∨l h h₁) (∧l₂ g) vg vh =
  let intrp E l k vl vk = mip h
      intrp E₁ l₁ k₁ vl₁ vk₁ = mip h₁
      f , eq , p = intrp-cut-witness' E l (cut k (∧l₂ g)) vl (λ q → vh (vk q))
      f₁ , eq₁ , p₁ = intrp-cut-witness' E₁ l₁ (cut k₁ (∧l₂ g)) vl₁ (λ q → vh (vk₁ q))
  in ∨l f f₁ , ∨l (eq ∙ cut-mip-left h (∧l₂ g)) (eq₁ ∙ cut-mip-left h₁ (∧l₂ g)) ,
     ↜∷ {n' = ∨l~' (intrp E l (cut k (∧l₂ g)) vl (λ q → vh (vk q)))
                    (intrp E₁ l₁ (cut k₁ (∧l₂ g)) vl₁ (λ q → vh (vk₁ q)))}
       (∨l k k₁ , ∨l (cut-intrp h) (cut-intrp h₁) , ~ cut∨l≗ k k₁ (∧l₂ g)) (∨l~ p p₁)
intrp-cut-witness' D h (∨r₁ g) vg vh =
  let intrp E l k vl vk = mip g
      f , eq , p = intrp-cut-witness' E (cut h l) k (λ q → vg (vl q)) vk
  in ∨r₁ f , ∨r₁ (eq ∙ cut-mip-right h g) ,
     ↝∷ {n' = ∨r₁~' (intrp E (cut h l) k (λ q → vg (vl q)) vk)}
       (l , refl , ∨r₁ (~ cut-intrp g)) (∨r₁~ p)
intrp-cut-witness' D h (∨r₂ g) vg vh =
  let intrp E l k vl vk = mip g
      f , eq , p = intrp-cut-witness' E (cut h l) k (λ q → vg (vl q)) vk
  in ∨r₂ f , ∨r₂ (eq ∙ cut-mip-right h g) ,
     ↝∷ {n' = ∨r₂~' (intrp E (cut h l) k (λ q → vg (vl q)) vk)}
       (l , refl , ∨r₂ (~ cut-intrp g)) (∨r₂~ p)
intrp-cut-witness' D ax (∨l g g₁) vg vh =
  let intrp E l k vl vk = mip (∨l g g₁)
  in ∨l g g₁ , refl ,
     ↝∷ {n' = intrp E l k vl vk}
       (l , cutaxA-left l , ~ cut-intrp (∨l g g₁)) refl
intrp-cut-witness' D ⊥l (∨l g g₁) vg vh =
  ⊥l , refl ,
  ↜∷ {n' = intrp ⊥ ax ⊥l (λ ()) (λ ())} (⊥l , refl , refl) refl
intrp-cut-witness' D (∧l₁ h) (∨l g g₁) vg vh =
  let intrp E l k vl vk = mip h
      f , eq , p = intrp-cut-witness' E l (cut k (∨l g g₁)) vl (λ q → vh (vk q))
  in ∧l₁ f , ∧l₁ (eq ∙ cut-mip-left h (∨l g g₁)) ,
     ↜∷ {n' = ∧l₁~' (intrp E l (cut k (∨l g g₁)) vl (λ q → vh (vk q)))}
       (k , cut∧l₁≗ l k ∙ ∧l₁ (cut-intrp h) , refl) (∧l₁~ p)
intrp-cut-witness' D (∧l₂ h) (∨l g g₁) vg vh =
  let intrp E l k vl vk = mip h
      f , eq , p = intrp-cut-witness' E l (cut k (∨l g g₁)) vl (λ q → vh (vk q))
  in ∧l₂ f , ∧l₂ (eq ∙ cut-mip-left h (∨l g g₁)) ,
     ↜∷ {n' = ∧l₂~' (intrp E l (cut k (∨l g g₁)) vl (λ q → vh (vk q)))}
       (k , cut∧l₂≗ l k ∙ ∧l₂ (cut-intrp h) , refl) (∧l₂~ p)
intrp-cut-witness' D (∨r₁ h) (∨l g g₁) vg vh =
  let f , eq , p = intrp-cut-witness' _ h g (λ q → vg (inj₁ q)) (λ q → vh (inj₁ q))
  in f , eq ,
     ↜∷ {n' = intrp _ h g (λ q → vg (inj₁ q)) (λ q → vh (inj₁ q))}
       (∨r₁ ax , refl , ~ cutaxA-left g) p
intrp-cut-witness' D (∨r₂ h) (∨l g g₁) vg vh =
  let f , eq , p = intrp-cut-witness' _ h g₁ (λ q → vg (inj₂ q)) (λ q → vh (inj₂ q))
  in f , eq ,
     ↜∷ {n' = intrp _ h g₁ (λ q → vg (inj₂ q)) (λ q → vh (inj₂ q))}
       (∨r₂ ax , refl , ~ cutaxA-left g₁) p

intrp-cut-witness' D (∨l h h₁) (∨l g g₁) vg vh =
  let intrp E l k vl vk = mip (∨l g g₁)
      intrp F n m vn vm = mip (cut h l)
      intrp F₁ n₁ m₁ vn₁ vm₁ = mip (cut h₁ l)
      f , eq , p = intrp-cut-witness' F n (cut m k) vn (λ q → vk (vm q))
      f₁ , eq₁ , p₁ = intrp-cut-witness' F₁ n₁ (cut m₁ k) vn₁ (λ q → vk (vm₁ q))
  in ∨l f f₁
   , ∨l
       (eq ∙ cut-mip-left (cut h l) k
           ∙ cut-mip-right h (∨l g g₁))
       (eq₁ ∙ cut-mip-left (cut h₁ l) k
            ∙ cut-mip-right h₁ (∨l g g₁))
   , ↝∷ {n' = intrp E (cut (∨l h h₁) l) k (λ q → vg (vl q)) vk}
       (l , refl , ~ cut-intrp (∨l g g₁))
       (↜∷
         {n' = ∨l~' (intrp F n (cut m k) vn (λ q → vk (vm q)))
                    (intrp F₁ n₁ (cut m₁ k) vn₁ (λ q → vk (vm₁ q)))}
         ( ∨l m m₁
         , ∨l (cut-intrp (cut h l)) (cut-intrp (cut h₁ l))
         , ~ cut∨l≗ m m₁ k
         )
         (∨l~ p p₁))

intrp-cut-witness : ∀ {A C}
  → (n : MIP A C)
  → Σ (A ⊢ C) λ f → (f ≗ cut (n .MIP.g) (n .MIP.h)) × (n ~ mip f)
intrp-cut-witness (intrp D h g vg vh) = intrp-cut-witness' D h g vg vh

intrp-cut : ∀ {A C}
  → (n : MIP A C)
  → n ~ mip (cut (n .MIP.g) (n .MIP.h))
intrp-cut n =
  let f , eq , p = intrp-cut-witness n
  in ~-trans p (mip≗ eq)
