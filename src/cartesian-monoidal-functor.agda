{-# OPTIONS --prop --postfix-projections --safe #-}

open import prop-setoid using (module ≈-Reasoning)
open import categories
  using (Category; HasTerminal; HasProducts; Product; IsProduct; IsTerminal)
open import monoidal-product
  using (MonoidalProduct; SymmetricMonoidal; MonoidalFunctor; LaxMonoidalFunctor)
open import functor using (Functor)
open import finite-product-functor using (FPFunctor)

module cartesian-monoidal-functor
  {o₁ m₁ e₁ o₂ m₂ e₂}
  (𝒞 : Category o₁ m₁ e₁) (𝒞-terminal : HasTerminal 𝒞) (𝒞-products : HasProducts 𝒞)
  (𝒟 : Category o₂ m₂ e₂) (𝒟-terminal : HasTerminal 𝒟) (𝒟-products : HasProducts 𝒟)
  (F  : Functor 𝒞 𝒟)     (FP : FPFunctor F)
  where

private
  module 𝒟 = Category 𝒟
  module 𝒞 = Category 𝒞

open import cartesian-monoidal 𝒞 𝒞-terminal 𝒞-products
  using ()
  renaming (×-monoidal to 𝒞-monoidal)

open import cartesian-monoidal 𝒟 𝒟-terminal 𝒟-products
  using ()
  renaming (×-monoidal to 𝒟-monoidal)

open MonoidalProduct
open MonoidalFunctor
open LaxMonoidalFunctor
open Functor
open FPFunctor
open Category.IsIso

F-monoidal : MonoidalFunctor 𝒞-monoidal 𝒟-monoidal F
F-monoidal .lax-monoidal .mult {X} {Y} =
  pair (HasProducts.p₁ 𝒟-products) (HasProducts.p₂ 𝒟-products)
  where module P = Product (HasProducts.getProduct 𝒞-products X Y)
        open IsProduct (FP .preserve-products _ _ P.prod P.p₁ P.p₂ P.isProduct)
F-monoidal .lax-monoidal .unit = to-terminal
  where open IsTerminal (FP .preserve-terminal _ (HasTerminal.isTerminal 𝒞-terminal))
F-monoidal .lax-monoidal .mult-natural {x₁} {x₂} {y₁} {y₂} f g = begin
    PFx₂Fy₂.pair (HasProducts.p₁ 𝒟-products) (HasProducts.p₂ 𝒟-products) 𝒟.∘ HasProducts.prod-m 𝒟-products (F .fmor f) (F .fmor g)
  ≈⟨ PFx₂Fy₂.pair-natural _ _ _ ⟩
    PFx₂Fy₂.pair (HasProducts.p₁ 𝒟-products 𝒟.∘ HasProducts.prod-m 𝒟-products (F .fmor f) (F .fmor g)) (HasProducts.p₂ 𝒟-products 𝒟.∘ HasProducts.prod-m 𝒟-products (F .fmor f) (F .fmor g))
  ≈⟨ PFx₂Fy₂.pair-cong (HasProducts.pair-p₁ 𝒟-products _ _) (HasProducts.pair-p₂ 𝒟-products _ _) ⟩
    PFx₂Fy₂.pair (F .fmor f 𝒟.∘ HasProducts.p₁ 𝒟-products) (F .fmor g 𝒟.∘ HasProducts.p₂ 𝒟-products)
  ≈˘⟨ PFx₂Fy₂.pair-cong (𝒟.∘-cong 𝒟.≈-refl (PFx₁Fy₁.pair-p₁ _ _)) (𝒟.∘-cong 𝒟.≈-refl (PFx₁Fy₁.pair-p₂ _ _)) ⟩
    PFx₂Fy₂.pair (F .fmor f 𝒟.∘ (F .fmor (HasProducts.p₁ 𝒞-products) 𝒟.∘ PFx₁Fy₁.pair (HasProducts.p₁ 𝒟-products) (HasProducts.p₂ 𝒟-products)))
                 (F .fmor g 𝒟.∘ (F .fmor (HasProducts.p₂ 𝒞-products) 𝒟.∘ PFx₁Fy₁.pair (HasProducts.p₁ 𝒟-products) (HasProducts.p₂ 𝒟-products)))
  ≈˘⟨ PFx₂Fy₂.pair-cong (𝒟.assoc _ _ _) (𝒟.assoc _ _ _) ⟩
    PFx₂Fy₂.pair ((F .fmor f 𝒟.∘ F .fmor (HasProducts.p₁ 𝒞-products)) 𝒟.∘ PFx₁Fy₁.pair (HasProducts.p₁ 𝒟-products) (HasProducts.p₂ 𝒟-products))
                 ((F .fmor g 𝒟.∘ F .fmor (HasProducts.p₂ 𝒞-products)) 𝒟.∘ PFx₁Fy₁.pair (HasProducts.p₁ 𝒟-products) (HasProducts.p₂ 𝒟-products))
  ≈˘⟨ PFx₂Fy₂.pair-cong (𝒟.∘-cong (F .fmor-comp _ _) 𝒟.≈-refl) (𝒟.∘-cong (F .fmor-comp _ _) 𝒟.≈-refl) ⟩
    PFx₂Fy₂.pair (F .fmor (f 𝒞.∘ HasProducts.p₁ 𝒞-products) 𝒟.∘ PFx₁Fy₁.pair (HasProducts.p₁ 𝒟-products) (HasProducts.p₂ 𝒟-products))
                 (F .fmor (g 𝒞.∘ HasProducts.p₂ 𝒞-products) 𝒟.∘ PFx₁Fy₁.pair (HasProducts.p₁ 𝒟-products) (HasProducts.p₂ 𝒟-products))
  ≈˘⟨ PFx₂Fy₂.pair-cong (𝒟.∘-cong (F .fmor-cong (HasProducts.pair-p₁ 𝒞-products _ _)) 𝒟.≈-refl)
                       (𝒟.∘-cong (F .fmor-cong (HasProducts.pair-p₂ 𝒞-products _ _)) 𝒟.≈-refl) ⟩
    PFx₂Fy₂.pair (F .fmor (HasProducts.p₁ 𝒞-products 𝒞.∘ HasProducts.prod-m 𝒞-products f g) 𝒟.∘ PFx₁Fy₁.pair (HasProducts.p₁ 𝒟-products) (HasProducts.p₂ 𝒟-products))
                 (F .fmor (HasProducts.p₂ 𝒞-products 𝒞.∘ HasProducts.prod-m 𝒞-products f g) 𝒟.∘ PFx₁Fy₁.pair (HasProducts.p₁ 𝒟-products) (HasProducts.p₂ 𝒟-products))
  ≈⟨ PFx₂Fy₂.pair-cong (𝒟.∘-cong (F .fmor-comp _ _) 𝒟.≈-refl) (𝒟.∘-cong (F .fmor-comp _ _) 𝒟.≈-refl) ⟩
    PFx₂Fy₂.pair ((F .fmor (HasProducts.p₁ 𝒞-products) 𝒟.∘ F .fmor (HasProducts.prod-m 𝒞-products f g)) 𝒟.∘ PFx₁Fy₁.pair (HasProducts.p₁ 𝒟-products) (HasProducts.p₂ 𝒟-products))
                 ((F .fmor (HasProducts.p₂ 𝒞-products) 𝒟.∘ F .fmor (HasProducts.prod-m 𝒞-products f g)) 𝒟.∘ PFx₁Fy₁.pair (HasProducts.p₁ 𝒟-products) (HasProducts.p₂ 𝒟-products))
  ≈⟨ PFx₂Fy₂.pair-cong (𝒟.assoc _ _ _) (𝒟.assoc _ _ _) ⟩
    PFx₂Fy₂.pair (F .fmor (HasProducts.p₁ 𝒞-products) 𝒟.∘ (F .fmor (HasProducts.prod-m 𝒞-products f g) 𝒟.∘ PFx₁Fy₁.pair (HasProducts.p₁ 𝒟-products) (HasProducts.p₂ 𝒟-products)))
                 (F .fmor (HasProducts.p₂ 𝒞-products) 𝒟.∘ (F .fmor (HasProducts.prod-m 𝒞-products f g) 𝒟.∘ PFx₁Fy₁.pair (HasProducts.p₁ 𝒟-products) (HasProducts.p₂ 𝒟-products)))
  ≈⟨ PFx₂Fy₂.pair-ext _ ⟩
    F .fmor (HasProducts.prod-m 𝒞-products f g) 𝒟.∘ PFx₁Fy₁.pair (HasProducts.p₁ 𝒟-products) (HasProducts.p₂ 𝒟-products)
  ∎
  where open ≈-Reasoning 𝒟.isEquiv
        module Px₁y₁ = Product (HasProducts.getProduct 𝒞-products x₁ y₁)
        module PFx₁Fy₁ = IsProduct (FP .preserve-products _ _ Px₁y₁.prod Px₁y₁.p₁ Px₁y₁.p₂ Px₁y₁.isProduct)
        module Px₂y₂ = Product (HasProducts.getProduct 𝒞-products x₂ y₂)
        module PFx₂Fy₂ = IsProduct (FP .preserve-products _ _ Px₂y₂.prod Px₂y₂.p₁ Px₂y₂.p₂ Px₂y₂.isProduct)
F-monoidal .lax-monoidal .mult-assoc = {!!}
F-monoidal .lax-monoidal .mult-lunit = {!!}
F-monoidal .lax-monoidal .mult-runit = {!!}
F-monoidal .mult-is-iso .inverse =
  HasProducts.pair 𝒟-products (F .fmor (HasProducts.p₁ 𝒞-products))
                               (F .fmor (HasProducts.p₂ 𝒞-products))
F-monoidal .mult-is-iso .f∘inverse≈id = {!!}
F-monoidal .mult-is-iso .inverse∘f≈id = {!!}
F-monoidal .unit-is-iso = {!!}
