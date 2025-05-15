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
  module 𝒟P = HasProducts 𝒟-products
  module 𝒞 = Category 𝒞
  module 𝒞P = HasProducts 𝒞-products
  module 𝒞T = HasTerminal 𝒞-terminal

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
F-monoidal .lax-monoidal .mult {X} {Y} = pair 𝒟P.p₁ 𝒟P.p₂
  where module P = Product (HasProducts.getProduct 𝒞-products X Y)
        open IsProduct (FP .preserve-products _ _ P.prod P.p₁ P.p₂ P.isProduct)
F-monoidal .lax-monoidal .unit = to-terminal
  where open IsTerminal (FP .preserve-terminal _ (HasTerminal.isTerminal 𝒞-terminal))

F-monoidal .lax-monoidal .mult-natural {x₁} {x₂} {y₁} {y₂} f g = begin
    PFx₂Fy₂.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.prod-m (F .fmor f) (F .fmor g)
  ≈⟨ PFx₂Fy₂.pair-natural _ _ _ ⟩
    PFx₂Fy₂.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.prod-m (F .fmor f) (F .fmor g)) (𝒟P.p₂ 𝒟.∘ 𝒟P.prod-m (F .fmor f) (F .fmor g))
  ≈⟨ PFx₂Fy₂.pair-cong (𝒟P.pair-p₁ _ _) (𝒟P.pair-p₂ _ _) ⟩
    PFx₂Fy₂.pair (F .fmor f 𝒟.∘ 𝒟P.p₁) (F .fmor g 𝒟.∘ 𝒟P.p₂)
  ≈˘⟨ PFx₂Fy₂.pair-cong (𝒟.∘-cong 𝒟.≈-refl (PFx₁Fy₁.pair-p₁ _ _)) (𝒟.∘-cong 𝒟.≈-refl (PFx₁Fy₁.pair-p₂ _ _)) ⟩
    PFx₂Fy₂.pair (F .fmor f 𝒟.∘ (F .fmor 𝒞P.p₁ 𝒟.∘ PFx₁Fy₁.pair 𝒟P.p₁ 𝒟P.p₂))
                 (F .fmor g 𝒟.∘ (F .fmor 𝒞P.p₂ 𝒟.∘ PFx₁Fy₁.pair 𝒟P.p₁ 𝒟P.p₂))
  ≈˘⟨ PFx₂Fy₂.pair-cong (𝒟.assoc _ _ _) (𝒟.assoc _ _ _) ⟩
    PFx₂Fy₂.pair ((F .fmor f 𝒟.∘ F .fmor 𝒞P.p₁) 𝒟.∘ PFx₁Fy₁.pair 𝒟P.p₁ 𝒟P.p₂)
                 ((F .fmor g 𝒟.∘ F .fmor 𝒞P.p₂) 𝒟.∘ PFx₁Fy₁.pair 𝒟P.p₁ 𝒟P.p₂)
  ≈˘⟨ PFx₂Fy₂.pair-cong (𝒟.∘-cong (F .fmor-comp _ _) 𝒟.≈-refl) (𝒟.∘-cong (F .fmor-comp _ _) 𝒟.≈-refl) ⟩
    PFx₂Fy₂.pair (F .fmor (f 𝒞.∘ 𝒞P.p₁) 𝒟.∘ PFx₁Fy₁.pair 𝒟P.p₁ 𝒟P.p₂)
                 (F .fmor (g 𝒞.∘ 𝒞P.p₂) 𝒟.∘ PFx₁Fy₁.pair 𝒟P.p₁ 𝒟P.p₂)
  ≈˘⟨ PFx₂Fy₂.pair-cong (𝒟.∘-cong (F .fmor-cong (𝒞P.pair-p₁ _ _)) 𝒟.≈-refl)
                       (𝒟.∘-cong (F .fmor-cong (𝒞P.pair-p₂ _ _)) 𝒟.≈-refl) ⟩
    PFx₂Fy₂.pair (F .fmor (𝒞P.p₁ 𝒞.∘ 𝒞P.prod-m f g) 𝒟.∘ PFx₁Fy₁.pair 𝒟P.p₁ 𝒟P.p₂)
                 (F .fmor (𝒞P.p₂ 𝒞.∘ 𝒞P.prod-m f g) 𝒟.∘ PFx₁Fy₁.pair 𝒟P.p₁ 𝒟P.p₂)
  ≈⟨ PFx₂Fy₂.pair-cong (𝒟.∘-cong (F .fmor-comp _ _) 𝒟.≈-refl) (𝒟.∘-cong (F .fmor-comp _ _) 𝒟.≈-refl) ⟩
    PFx₂Fy₂.pair ((F .fmor 𝒞P.p₁ 𝒟.∘ F .fmor (𝒞P.prod-m f g)) 𝒟.∘ PFx₁Fy₁.pair 𝒟P.p₁ 𝒟P.p₂)
                 ((F .fmor 𝒞P.p₂ 𝒟.∘ F .fmor (𝒞P.prod-m f g)) 𝒟.∘ PFx₁Fy₁.pair 𝒟P.p₁ 𝒟P.p₂)
  ≈⟨ PFx₂Fy₂.pair-cong (𝒟.assoc _ _ _) (𝒟.assoc _ _ _) ⟩
    PFx₂Fy₂.pair (F .fmor 𝒞P.p₁ 𝒟.∘ (F .fmor (𝒞P.prod-m f g) 𝒟.∘ PFx₁Fy₁.pair 𝒟P.p₁ 𝒟P.p₂))
                 (F .fmor 𝒞P.p₂ 𝒟.∘ (F .fmor (𝒞P.prod-m f g) 𝒟.∘ PFx₁Fy₁.pair 𝒟P.p₁ 𝒟P.p₂))
  ≈⟨ PFx₂Fy₂.pair-ext _ ⟩
    F .fmor (𝒞P.prod-m f g) 𝒟.∘ PFx₁Fy₁.pair 𝒟P.p₁ 𝒟P.p₂
  ∎
  where open ≈-Reasoning 𝒟.isEquiv
        module Px₁y₁ = Product (HasProducts.getProduct 𝒞-products x₁ y₁)
        module PFx₁Fy₁ = IsProduct (FP .preserve-products _ _ Px₁y₁.prod Px₁y₁.p₁ Px₁y₁.p₂ Px₁y₁.isProduct)
        module Px₂y₂ = Product (HasProducts.getProduct 𝒞-products x₂ y₂)
        module PFx₂Fy₂ = IsProduct (FP .preserve-products _ _ Px₂y₂.prod Px₂y₂.p₁ Px₂y₂.p₂ Px₂y₂.isProduct)
F-monoidal .lax-monoidal .mult-assoc {x} {y} {z} = begin
    PFxFyz.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ (𝒟P.pair (𝒟.id _ 𝒟.∘ 𝒟P.p₁) (PFyFz.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₂) 𝒟.∘ 𝒟P.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.p₁) (𝒟P.pair (𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂))
  ≈⟨ PFxFyz.pair-natural _ _ _ ⟩
    PFxFyz.pair (𝒟P.p₁ 𝒟.∘ (𝒟P.pair (𝒟.id _ 𝒟.∘ 𝒟P.p₁) (PFyFz.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₂) 𝒟.∘ 𝒟P.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.p₁) (𝒟P.pair (𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂)))
                (𝒟P.p₂ 𝒟.∘ (𝒟P.pair (𝒟.id _ 𝒟.∘ 𝒟P.p₁) (PFyFz.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₂) 𝒟.∘ 𝒟P.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.p₁) (𝒟P.pair (𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂)))
  ≈˘⟨ PFxFyz.pair-cong (𝒟.assoc _ _ _) (𝒟.assoc _ _ _) ⟩
    PFxFyz.pair ((𝒟P.p₁ 𝒟.∘ 𝒟P.pair (𝒟.id _ 𝒟.∘ 𝒟P.p₁) (PFyFz.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₂)) 𝒟.∘ 𝒟P.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.p₁) (𝒟P.pair (𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂))
                ((𝒟P.p₂ 𝒟.∘ 𝒟P.pair (𝒟.id _ 𝒟.∘ 𝒟P.p₁) (PFyFz.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₂)) 𝒟.∘ 𝒟P.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.p₁) (𝒟P.pair (𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂))
  ≈⟨ PFxFyz.pair-cong (𝒟.∘-cong (𝒟P.pair-p₁ _ _) 𝒟.≈-refl) (𝒟.∘-cong (𝒟P.pair-p₂ _ _) 𝒟.≈-refl) ⟩
    PFxFyz.pair ((𝒟.id _ 𝒟.∘ 𝒟P.p₁) 𝒟.∘ 𝒟P.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.p₁) (𝒟P.pair (𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂))
                ((PFyFz.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₂) 𝒟.∘ 𝒟P.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.p₁) (𝒟P.pair (𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂))
  ≈⟨ PFxFyz.pair-cong (𝒟.∘-cong 𝒟.id-left 𝒟.≈-refl) (𝒟.assoc _ _ _) ⟩
    PFxFyz.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.p₁) (𝒟P.pair (𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂))
                (PFyFz.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ (𝒟P.p₂ 𝒟.∘ 𝒟P.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.p₁) (𝒟P.pair (𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂)))
  ≈⟨ PFxFyz.pair-cong (𝒟P.pair-p₁ _ _) (𝒟.∘-cong 𝒟.≈-refl (𝒟P.pair-p₂ _ _)) ⟩
    PFxFyz.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.p₁)
                (PFyFz.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.pair (𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂)
  ≈⟨ PFxFyz.pair-cong 𝒟.≈-refl (PFyFz.pair-natural _ _ _) ⟩
    PFxFyz.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.p₁)
                (PFyFz.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.pair (𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂) (𝒟P.p₂ 𝒟.∘ 𝒟P.pair (𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂))
  ≈⟨ PFxFyz.pair-cong 𝒟.≈-refl (PFyFz.pair-cong (𝒟P.pair-p₁ _ _) (𝒟P.pair-p₂ _ _)) ⟩
    PFxFyz.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.p₁)
                (PFyFz.pair (𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂)
  ≈˘⟨ PFxFyz.pair-cong 𝒟.≈-refl (PFyFz.pair-cong (𝒟.∘-cong (PFxFy.pair-p₂ _ _) 𝒟.≈-refl) 𝒟.≈-refl) ⟩
    PFxFyz.pair
      (𝒟P.p₁ 𝒟.∘ 𝒟P.p₁)
      (PFyFz.pair ((F .fmor 𝒞P.p₂ 𝒟.∘ PFxFy.pair 𝒟P.p₁ 𝒟P.p₂) 𝒟.∘ 𝒟P.p₁)
                  𝒟P.p₂)
  ≈⟨ PFxFyz.pair-cong 𝒟.≈-refl (PFyFz.pair-cong (𝒟.assoc _ _ _) 𝒟.≈-refl) ⟩
    PFxFyz.pair
      (𝒟P.p₁ 𝒟.∘ 𝒟P.p₁)
      (PFyFz.pair (F .fmor 𝒞P.p₂ 𝒟.∘ (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁))
                  𝒟P.p₂)
  ≈˘⟨ PFxFyz.pair-cong (𝒟.∘-cong (PFxFy.pair-p₁ _ _) 𝒟.≈-refl) (PFyFz.pair-cong (𝒟.∘-cong 𝒟.≈-refl (PFxyFz.pair-p₁ _ _)) 𝒟.≈-refl) ⟩
    PFxFyz.pair
      ((F .fmor 𝒞P.p₁ 𝒟.∘ PFxFy.pair 𝒟P.p₁ 𝒟P.p₂) 𝒟.∘ 𝒟P.p₁)
      (PFyFz.pair (F .fmor 𝒞P.p₂ 𝒟.∘ (F .fmor 𝒞P.p₁ 𝒟.∘ PFxyFz.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂))
                  𝒟P.p₂)
  ≈⟨ PFxFyz.pair-cong (𝒟.assoc _ _ _) (PFyFz.pair-cong (𝒟.≈-sym (𝒟.assoc _ _ _)) 𝒟.≈-refl) ⟩
    PFxFyz.pair
      (F .fmor 𝒞P.p₁ 𝒟.∘ (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁))
      (PFyFz.pair ((F .fmor 𝒞P.p₂ 𝒟.∘ F .fmor 𝒞P.p₁) 𝒟.∘ PFxyFz.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂)
                  𝒟P.p₂)
  ≈˘⟨ PFxFyz.pair-cong (𝒟.∘-cong 𝒟.≈-refl (PFxyFz.pair-p₁ _ _)) (PFyFz.pair-cong (𝒟.∘-cong (F .fmor-comp _ _) 𝒟.≈-refl) (PFxyFz.pair-p₂ _ _)) ⟩
    PFxFyz.pair
      (F .fmor 𝒞P.p₁ 𝒟.∘ (F .fmor 𝒞P.p₁ 𝒟.∘ PFxyFz.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂))
      (PFyFz.pair (F .fmor (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁) 𝒟.∘ PFxyFz.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂)
                  (F .fmor 𝒞P.p₂ 𝒟.∘ PFxyFz.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂))
  ≈˘⟨ PFxFyz.pair-cong (𝒟.assoc _ _ _) (PFyFz.pair-natural _ _ _) ⟩
    PFxFyz.pair
      ((F .fmor 𝒞P.p₁ 𝒟.∘ F .fmor 𝒞P.p₁) 𝒟.∘ PFxyFz.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂)
      (PFyFz.pair (F .fmor (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁)) (F .fmor 𝒞P.p₂) 𝒟.∘ PFxyFz.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂)
  ≈˘⟨ PFxFyz.pair-natural _ _ _ ⟩
    PFxFyz.pair (F .fmor 𝒞P.p₁ 𝒟.∘ F .fmor 𝒞P.p₁) (PFyFz.pair (F .fmor (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁)) (F .fmor 𝒞P.p₂))
      𝒟.∘ PFxyFz.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂
  ≈˘⟨ 𝒟.∘-cong (PFxFyz.pair-cong 𝒟.≈-refl (PFyFz.pair-cong (F .fmor-cong (𝒞P.pair-p₁ _ _)) (F .fmor-cong (𝒞P.pair-p₂ _ _)))) 𝒟.≈-refl ⟩
    PFxFyz.pair (F .fmor 𝒞P.p₁ 𝒟.∘ F .fmor 𝒞P.p₁) (PFyFz.pair (F .fmor (𝒞P.p₁ 𝒞.∘ 𝒞P.pair (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁) 𝒞P.p₂))
                                                                (F .fmor (𝒞P.p₂ 𝒞.∘ 𝒞P.pair (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁) 𝒞P.p₂)))
      𝒟.∘ PFxyFz.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂
  ≈⟨ 𝒟.∘-cong (PFxFyz.pair-cong 𝒟.≈-refl (PFyFz.pair-cong (F .fmor-comp _ _) (F .fmor-comp _ _))) 𝒟.≈-refl ⟩
    PFxFyz.pair (F .fmor 𝒞P.p₁ 𝒟.∘ F .fmor 𝒞P.p₁) (PFyFz.pair (F .fmor 𝒞P.p₁ 𝒟.∘ F .fmor (𝒞P.pair (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁) 𝒞P.p₂))
                                                                (F .fmor 𝒞P.p₂ 𝒟.∘ F .fmor (𝒞P.pair (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁) 𝒞P.p₂)))
      𝒟.∘ PFxyFz.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂
  ≈˘⟨ 𝒟.∘-cong (PFxFyz.pair-cong (F .fmor-comp _ _) (𝒟.≈-sym (PFyFz.pair-ext _))) 𝒟.≈-refl ⟩
    PFxFyz.pair (F .fmor (𝒞P.p₁ 𝒞.∘ 𝒞P.p₁)) (F .fmor (𝒞P.pair (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁) 𝒞P.p₂))
      𝒟.∘ PFxyFz.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂
  ≈˘⟨ 𝒟.∘-cong (PFxFyz.pair-cong (F .fmor-cong (𝒞P.pair-p₁ _ _)) (F .fmor-cong (𝒞P.pair-p₂ _ _))) 𝒟.≈-refl ⟩
    PFxFyz.pair (F .fmor (𝒞P.p₁ 𝒞.∘ 𝒞P.pair (𝒞P.p₁ 𝒞.∘ 𝒞P.p₁) (𝒞P.pair (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁) 𝒞P.p₂)))
                (F .fmor (𝒞P.p₂ 𝒞.∘ 𝒞P.pair (𝒞P.p₁ 𝒞.∘ 𝒞P.p₁) (𝒞P.pair (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁) 𝒞P.p₂)))
      𝒟.∘ PFxyFz.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂
  ≈⟨ 𝒟.∘-cong (PFxFyz.pair-cong (F .fmor-comp _ _) (F .fmor-comp _ _)) 𝒟.≈-refl ⟩
    PFxFyz.pair (F .fmor 𝒞P.p₁ 𝒟.∘ F .fmor (𝒞P.pair (𝒞P.p₁ 𝒞.∘ 𝒞P.p₁) (𝒞P.pair (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁) 𝒞P.p₂)))
                (F .fmor 𝒞P.p₂ 𝒟.∘ F .fmor (𝒞P.pair (𝒞P.p₁ 𝒞.∘ 𝒞P.p₁) (𝒞P.pair (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁) 𝒞P.p₂)))
      𝒟.∘ PFxyFz.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂
  ≈⟨ 𝒟.∘-cong (PFxFyz.pair-ext _) 𝒟.≈-refl ⟩
    F .fmor (𝒞P.pair (𝒞P.p₁ 𝒞.∘ 𝒞P.p₁) (𝒞P.pair (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁) 𝒞P.p₂)) 𝒟.∘ PFxyFz.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) 𝒟P.p₂
  ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (PFxyFz.pair-cong 𝒟.≈-refl 𝒟.id-left) ⟩
    F .fmor (𝒞P.pair (𝒞P.p₁ 𝒞.∘ 𝒞P.p₁) (𝒞P.pair (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁) 𝒞P.p₂)) 𝒟.∘ PFxyFz.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) (𝒟.id _ 𝒟.∘ 𝒟P.p₂)
  ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (PFxyFz.pair-cong (𝒟P.pair-p₁ _ _) (𝒟P.pair-p₂ _ _)) ⟩
    F .fmor (𝒞P.pair (𝒞P.p₁ 𝒞.∘ 𝒞P.p₁) (𝒞P.pair (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁) 𝒞P.p₂)) 𝒟.∘ PFxyFz.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) (𝒟.id _ 𝒟.∘ 𝒟P.p₂))
                                                                                                  (𝒟P.p₂ 𝒟.∘ 𝒟P.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) (𝒟.id _ 𝒟.∘ 𝒟P.p₂))
  ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (PFxyFz.pair-natural _ _ _) ⟩
    F .fmor (𝒞P.pair (𝒞P.p₁ 𝒞.∘ 𝒞P.p₁) (𝒞P.pair (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁) 𝒞P.p₂)) 𝒟.∘ (PFxyFz.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.pair (PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.p₁) (𝒟.id _ 𝒟.∘ 𝒟P.p₂))
  ∎
  where open ≈-Reasoning 𝒟.isEquiv
        module Pxy = Product (𝒞P.getProduct x y)
        module Pyz = Product (𝒞P.getProduct y z)
        module PFxFy = IsProduct (FP .preserve-products _ _ (𝒞P.prod x y) 𝒞P.p₁ 𝒞P.p₂ Pxy.isProduct)
        module PFyFz = IsProduct (FP .preserve-products _ _ (𝒞P.prod y z) 𝒞P.p₁ 𝒞P.p₂ Pyz.isProduct)
        module PxPyz = Product (𝒞P.getProduct x (𝒞P.prod y z))
        module PxyPz = Product (𝒞P.getProduct (𝒞P.prod x y) z)
        module PFxFyz = IsProduct (FP .preserve-products _ _ (𝒞P.prod x (𝒞P.prod y z)) 𝒞P.p₁ 𝒞P.p₂ PxPyz.isProduct)
        module PFxyFz = IsProduct (FP .preserve-products _ _ (𝒞P.prod (𝒞P.prod x y) z) 𝒞P.p₁ 𝒞P.p₂ PxyPz.isProduct)
F-monoidal .lax-monoidal .mult-lunit {x} = begin
    PFIFx.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.prod-m to-terminal (𝒟.id _)
  ≈⟨ PFIFx.pair-natural _ _ _ ⟩
    PFIFx.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.prod-m to-terminal (𝒟.id _)) (𝒟P.p₂ 𝒟.∘ 𝒟P.prod-m to-terminal (𝒟.id _))
  ≈⟨ PFIFx.pair-cong (𝒟P.pair-p₁ _ _) (𝒟P.pair-p₂ _ _) ⟩
    PFIFx.pair (to-terminal 𝒟.∘ 𝒟P.p₁) (𝒟.id _ 𝒟.∘ 𝒟P.p₂)
  ≈˘⟨ PFIFx.pair-cong (to-terminal-ext _) 𝒟.≈-refl ⟩
    PFIFx.pair to-terminal (𝒟.id _ 𝒟.∘ 𝒟P.p₂)
  ≈⟨ PFIFx.pair-cong (to-terminal-ext _) (𝒟.∘-cong (𝒟.≈-sym (F .fmor-id)) 𝒟.≈-refl) ⟩
    PFIFx.pair (F .fmor (𝒞P.p₁ 𝒞.∘ 𝒞P.pair (𝒞T.terminal-mor x) (𝒞.id _)) 𝒟.∘ 𝒟P.p₂)
               (F .fmor (𝒞.id _) 𝒟.∘ 𝒟P.p₂)
  ≈˘⟨ PFIFx.pair-cong 𝒟.≈-refl (𝒟.∘-cong (F .fmor-cong (𝒞P.pair-p₂ _ _)) 𝒟.≈-refl) ⟩
    PFIFx.pair (F .fmor (𝒞P.p₁ 𝒞.∘ 𝒞P.pair (𝒞T.terminal-mor x) (𝒞.id _)) 𝒟.∘ 𝒟P.p₂)
               (F .fmor (𝒞P.p₂ 𝒞.∘ 𝒞P.pair (𝒞T.terminal-mor x) (𝒞.id _)) 𝒟.∘ 𝒟P.p₂)
  ≈⟨ PFIFx.pair-cong (𝒟.∘-cong (F .fmor-comp _ _) 𝒟.≈-refl) (𝒟.∘-cong (F .fmor-comp _ _) 𝒟.≈-refl) ⟩
    PFIFx.pair ((F .fmor 𝒞P.p₁ 𝒟.∘ F .fmor (𝒞P.pair (𝒞T.terminal-mor x) (𝒞.id _))) 𝒟.∘ 𝒟P.p₂)
               ((F .fmor 𝒞P.p₂ 𝒟.∘ F .fmor (𝒞P.pair (𝒞T.terminal-mor x) (𝒞.id _))) 𝒟.∘ 𝒟P.p₂)
  ≈⟨ PFIFx.pair-cong (𝒟.assoc _ _ _) (𝒟.assoc _ _ _) ⟩
    PFIFx.pair (F .fmor 𝒞P.p₁ 𝒟.∘ (F .fmor (𝒞P.pair (𝒞T.terminal-mor x) (𝒞.id _)) 𝒟.∘ 𝒟P.p₂))
               (F .fmor 𝒞P.p₂ 𝒟.∘ (F .fmor (𝒞P.pair (𝒞T.terminal-mor x) (𝒞.id _)) 𝒟.∘ 𝒟P.p₂))
  ≈⟨ PFIFx.pair-ext _ ⟩
    F .fmor (𝒞P.pair (𝒞T.terminal-mor x) (𝒞.id _)) 𝒟.∘ 𝒟P.p₂
  ∎
  where open ≈-Reasoning 𝒟.isEquiv
        module PIx = Product (𝒞P.getProduct (𝒞-monoidal .I⊗) x)
        module PFIFx = IsProduct (FP .preserve-products _ _ PIx.prod PIx.p₁ PIx.p₂ PIx.isProduct)
        open IsTerminal (FP .preserve-terminal _ (HasTerminal.isTerminal 𝒞-terminal))
F-monoidal .lax-monoidal .mult-runit = {!!}

F-monoidal .mult-is-iso .inverse =
  𝒟P.pair (F .fmor 𝒞P.p₁) (F .fmor 𝒞P.p₂)
F-monoidal .mult-is-iso {x} {y} .f∘inverse≈id = begin
    PFxFy.pair 𝒟P.p₁ 𝒟P.p₂ 𝒟.∘ 𝒟P.pair (F .fmor 𝒞P.p₁) (F .fmor 𝒞P.p₂)
  ≈⟨ PFxFy.pair-natural _ _ _ ⟩
    PFxFy.pair (𝒟P.p₁ 𝒟.∘ 𝒟P.pair (F .fmor 𝒞P.p₁) (F .fmor 𝒞P.p₂))
               (𝒟P.p₂ 𝒟.∘ 𝒟P.pair (F .fmor 𝒞P.p₁) (F .fmor 𝒞P.p₂))
  ≈⟨ PFxFy.pair-cong (𝒟P.pair-p₁ _ _) (𝒟P.pair-p₂ _ _) ⟩
    PFxFy.pair (F .fmor 𝒞P.p₁) (F .fmor 𝒞P.p₂)
  ≈⟨ PFxFy.pair-ext0 ⟩
    𝒟.id _
  ∎
  where open ≈-Reasoning 𝒟.isEquiv
        module Pxy = Product (HasProducts.getProduct 𝒞-products x y)
        module PFxFy = IsProduct (FP .preserve-products _ _ Pxy.prod Pxy.p₁ Pxy.p₂ Pxy.isProduct)
F-monoidal .mult-is-iso {x} {y} .inverse∘f≈id = begin
    𝒟P.pair (F .fmor (𝒞P.p₁)) (F .fmor (𝒞P.p₂)) 𝒟.∘ PFxFy.pair (𝒟P.p₁) 𝒟P.p₂
  ≈⟨ 𝒟P.pair-natural _ _ _ ⟩
    𝒟P.pair (F .fmor (𝒞P.p₁) 𝒟.∘ PFxFy.pair (𝒟P.p₁) 𝒟P.p₂)
             (F .fmor (𝒞P.p₂) 𝒟.∘ PFxFy.pair (𝒟P.p₁) 𝒟P.p₂)
  ≈⟨ 𝒟P.pair-cong (PFxFy.pair-p₁ _ _) (PFxFy.pair-p₂ _ _) ⟩
    𝒟P.pair 𝒟P.p₁ 𝒟P.p₂
  ≈⟨ 𝒟P.pair-ext0 ⟩
    𝒟.id _
  ∎
  where open ≈-Reasoning 𝒟.isEquiv
        module Pxy = Product (HasProducts.getProduct 𝒞-products x y)
        module PFxFy = IsProduct (FP .preserve-products _ _ Pxy.prod Pxy.p₁ Pxy.p₂ Pxy.isProduct)


F-monoidal .unit-is-iso .inverse = HasTerminal.terminal-mor 𝒟-terminal _
F-monoidal .unit-is-iso .f∘inverse≈id =
  𝒟.≈-trans (𝒟.≈-sym (to-terminal-ext _)) (to-terminal-ext _)
  where open IsTerminal (FP .preserve-terminal _ (HasTerminal.isTerminal 𝒞-terminal))
F-monoidal .unit-is-iso .inverse∘f≈id =
  𝒟.≈-trans (𝒟.≈-sym (to-terminal-ext _)) (to-terminal-ext _)
  where open IsTerminal (HasTerminal.isTerminal 𝒟-terminal)
