{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_; 0ℓ)
open import prop-setoid using (module ≈-Reasoning)
open import categories using (Category; IsTerminal; IsProduct; IsProduct-cong)
open import functor using (Functor; preserve-limits-of-shape; IsLimit;
                           NatIso; NatTrans; ≃-NatTrans; constFmor)

module finite-product-functor
  {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂}
  (F : Functor 𝒞 𝒟)
  where

private
  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟
  module F = Functor F

record FPFunctor : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  field
    preserve-terminal : ∀ t → IsTerminal 𝒞 t → IsTerminal 𝒟 (F.fobj t)
    preserve-products : ∀ (x y xy : 𝒞.obj)
      (p₁ : xy 𝒞.⇒ x) (p₂ : xy 𝒞.⇒ y) →
      IsProduct 𝒞 x y xy p₁ p₂ →
      IsProduct 𝒟 (F.fobj x) (F.fobj y) (F.fobj xy) (F.fmor p₁) (F.fmor p₂)

-- If a functor preserves the empty diagram, then it preserves terminal objects

open import empty-diagram using (limit→terminal; terminal→limit)
open import product-diagram using (limit→product; product→limit)

mk-preserve-terminal : preserve-limits-of-shape empty-diagram.cat F →
                       ∀ t → IsTerminal 𝒞 t → IsTerminal 𝒟 (F.fobj t)
mk-preserve-terminal F-preserve t t-terminal =
    limit→terminal 𝒟 (F-preserve _ t _ (terminal→limit 𝒞 t-terminal))

-- If a functor preserves product-shaped limits, then it preserves products

mk-preserve-products : preserve-limits-of-shape product-diagram.cat F →
                       ∀ (x y xy : 𝒞.obj) (p₁ : xy 𝒞.⇒ x) (p₂ : xy 𝒞.⇒ y) →
                       IsProduct 𝒞 x y xy p₁ p₂ →
                       IsProduct 𝒟 (F.fobj x) (F.fobj y) (F.fobj xy) (F.fmor p₁) (F.fmor p₂)
mk-preserve-products F-preserve x y xy p₁ p₂ is-product =
  IsProduct-cong 𝒟 (𝒟.≈-trans 𝒟.id-right 𝒟.id-left) (𝒟.≈-trans 𝒟.id-right 𝒟.id-left) (limit→product 𝒟 lim)
  where lim = F-preserve _ xy _ (product→limit 𝒞 is-product)

preserve-fp→FPFunctor : preserve-limits-of-shape empty-diagram.cat F →
                        preserve-limits-of-shape product-diagram.cat F →
                        FPFunctor
preserve-fp→FPFunctor preserve-empty preserve-product .FPFunctor.preserve-terminal = mk-preserve-terminal preserve-empty
preserve-fp→FPFunctor preserve-empty preserve-product .FPFunctor.preserve-products = mk-preserve-products preserve-product

continuous→FPFunctor : (∀ (𝒮 : Category 0ℓ 0ℓ 0ℓ) → preserve-limits-of-shape 𝒮 F) →
                       FPFunctor
continuous→FPFunctor preserve-all = preserve-fp→FPFunctor (preserve-all _) (preserve-all _)
