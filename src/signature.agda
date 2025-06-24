{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (suc; _⊔_)
open import Data.List using (List; []; _∷_; _++_)
open import categories using (Category; HasTerminal; HasProducts; IsProduct; IsTerminal; Product)

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
  open HasProducts products renaming (pair to ⟨_,_⟩; prod to _×_) public

  list→product : ∀ {ℓ} {A : Set ℓ} → (A → obj) → List A → obj
  list→product i []       = 𝟙
  list→product i (x ∷ xs) = i x × list→product i xs

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

open import functor

-- An FP Functor is one that preserves finite products
record FPFunctor {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} (F : Functor 𝒞 𝒟) : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
  open Functor F
  field
    preserve-terminal : ∀ t → IsTerminal 𝒞 t → IsTerminal 𝒟 (fobj t)
    preserve-products : ∀ (x y xy : 𝒞.obj)
      (p₁ : xy 𝒞.⇒ x) (p₂ : xy 𝒞.⇒ y) →
      IsProduct 𝒞 x y xy p₁ p₂ →
      IsProduct 𝒟 (fobj x) (fobj y) (fobj xy) (fmor p₁) (fmor p₂)

module _ {ℓ o₁ m₁ e₁ o₂ m₂ e₂}
         {𝒞 : PointedFPCat o₁ m₁ e₁}
         {𝒟 : PointedFPCat o₂ m₂ e₂}
         (Sig : Signature ℓ)
  where

  private
    module Sig = Signature Sig
    module 𝒞 = PointedFPCat 𝒞
    module 𝒟 = PointedFPCat 𝒟

  open Model
  open Functor
  open FPFunctor

  module _ (F : Functor 𝒞.cat 𝒟.cat)
           (FP : FPFunctor F)
           (Ω-mor : F .fobj 𝒞.Ω 𝒟.⇒ 𝒟.Ω)
    where

    transport-product : (f : Sig.sort → 𝒞.obj) →
        ∀ σs → 𝒟.list→product (λ σ → F .fobj (f σ)) σs 𝒟.⇒ F .fobj (𝒞.list→product f σs)
    transport-product f [] = to-terminal
      where
        open IsTerminal (FP .preserve-terminal _ (HasTerminal.is-terminal 𝒞.terminal))
    transport-product f (x ∷ σs) =
      pair (HasProducts.p₁ 𝒟.products)
           (transport-product f σs 𝒟.∘ HasProducts.p₂ 𝒟.products)
      where
       module P = Product (HasProducts.getProduct 𝒞.products (f x) (𝒞.list→product f σs))
       open IsProduct (FP .preserve-products _ _ P.prod P.p₁ P.p₂ P.isProduct)

    transport-model : Model 𝒞 Sig → Model 𝒟 Sig
    transport-model M .⟦sort⟧ σ = F .fobj (M .⟦sort⟧ σ)
    transport-model M .⟦op⟧ {σs} {σ} ω =
      F .fmor (M .⟦op⟧ ω) 𝒟.∘ transport-product (M .⟦sort⟧) σs
    transport-model M .⟦rel⟧ {σs} ρ =
      (Ω-mor 𝒟.∘ (F .fmor (M .⟦rel⟧ ρ))) 𝒟.∘ transport-product (M .⟦sort⟧) σs
