{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (suc; _⊔_)
open import Data.List using (List; []; _∷_)
open import categories using (Category; HasTerminal; HasProducts)

module signature where

record Signature ℓ : Set (suc ℓ) where
  field
    sort : Set ℓ
    op   : List sort → sort → Set ℓ
    rel  : List sort → Set ℓ


-- Models of signatures live in finite product (FIXME: monoidal?)
-- categories with a specified object of truth values.
record PointedFPCat o m e : Set (suc (o ⊔ m ⊔ e)) where
  constructor PFPC[_,_,_,_]
  field
    cat      : Category o m e
    terminal : HasTerminal cat
    products : HasProducts cat
    Ω        : Category.obj cat

  open Category cat public
  open HasTerminal terminal renaming (witness to 𝟙) public
  open HasProducts products renaming (pair to ⟨_,_⟩) public

  list→product : ∀ {ℓ} {A : Set ℓ} → (A → obj) → List A → obj
  list→product i [] = 𝟙
  list→product i (x ∷ xs) = prod (i x) (list→product i xs)

record Model {ℓ o m e} (𝒞 : PointedFPCat o m e) (Sig : Signature ℓ) : Set (ℓ ⊔ o ⊔ m) where
  open PointedFPCat 𝒞
  open Signature Sig
  field
    ⟦sort⟧ : sort → obj
    ⟦op⟧   : ∀ {i o} → op i o → list→product ⟦sort⟧ i ⇒ ⟦sort⟧ o
    ⟦rel⟧  : ∀ {i} → rel i → list→product ⟦sort⟧ i ⇒ Ω

  -- FIXME: morphisms of models: for each sort, a morphism between
  --   interpretations, such that all the operations and relations are
  --   preserved.
  --
  --   Get a category of models in the given category.

-- If F : 𝒞 ⇒ 𝒟 is a finite product preserving, point preserving
-- functor, then there is a map of Models : Model 𝒞 Sig → Model 𝒟 Sig
--
-- (and this is functorial.)
