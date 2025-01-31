{-# OPTIONS --prop --postfix-projections --safe #-}

open import prop-setoid using (module ≈-Reasoning)
open import categories
open import functor

module functor-cat-products
         {o₁ m₁ e₁ o₂ m₂ e₂}
         (𝒞 : Category o₁ m₁ e₁)
         (𝒟 : Category o₂ m₂ e₂)
         (P  : HasProducts 𝒟)
  where

open Functor
open NatTrans
open ≃-NatTrans

private
  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟
  module P = HasProducts P

_×_ : Functor 𝒞 𝒟 → Functor 𝒞 𝒟 → Functor 𝒞 𝒟
(F × G) .fobj x = P.prod (F .fobj x) (G .fobj x)
(F × G) .fmor f = P.prod-m (F .fmor f) (G .fmor f)
(F × G) .fmor-cong f≈g =
  P.prod-m-cong (F .fmor-cong f≈g) (G .fmor-cong f≈g)
(F × G) .fmor-id {x} =
  begin
    P.prod-m (F .fmor (𝒞.id x)) (G .fmor (𝒞.id x))
  ≈⟨ P.prod-m-cong (F .fmor-id) (G .fmor-id) ⟩
    P.prod-m (𝒟.id _) (𝒟.id _)
  ≈⟨ P.prod-m-id ⟩
    𝒟.id _
  ∎ where open ≈-Reasoning 𝒟.isEquiv
(F × G) .fmor-comp f g =
  begin
    P.prod-m (F .fmor (f 𝒞.∘ g)) (G .fmor (f 𝒞.∘ g))
  ≈⟨ P.prod-m-cong (F .fmor-comp _ _) (G .fmor-comp _ _) ⟩
    P.prod-m (F .fmor f 𝒟.∘ F .fmor g) (G .fmor f 𝒟.∘ G .fmor g)
  ≈⟨ P.pair-functorial _ _ _ _ ⟩
    P.prod-m (F .fmor f) (G .fmor f) 𝒟.∘ P.prod-m (F .fmor g) (G .fmor g)
  ∎ where open ≈-Reasoning 𝒟.isEquiv

products : HasProducts [ 𝒞 ⇒ 𝒟 ]
products .HasProducts.prod = _×_
products .HasProducts.p₁ .transf x = P.p₁
products .HasProducts.p₁ .natural f = 𝒟.≈-sym (P.pair-p₁ _ _)
products .HasProducts.p₂ .transf x = P.p₂
products .HasProducts.p₂ .natural f = 𝒟.≈-sym (P.pair-p₂ _ _)
products .HasProducts.pair α β .transf x = P.pair (α .transf x) (β .transf x)
products .HasProducts.pair {F} {G} {H} α β .natural {x} {y} f =
  begin
    P.prod-m (G .fmor f) (H .fmor f) 𝒟.∘ P.pair (α .transf x) (β .transf x)
  ≈⟨ P.pair-compose _ _ _ _ ⟩
    P.pair (G .fmor f 𝒟.∘ α .transf x) (H .fmor f 𝒟.∘ β .transf x)
  ≈⟨ P.pair-cong (α .natural f) (β .natural f) ⟩
    P.pair (α .transf y 𝒟.∘ F .fmor f) (β .transf y 𝒟.∘ F .fmor f)
  ≈⟨ 𝒟.≈-sym (P.pair-natural _ _ _) ⟩
    P.pair (α .transf y) (β .transf y) 𝒟.∘ F .fmor f
  ∎ where open ≈-Reasoning 𝒟.isEquiv
products .HasProducts.pair-cong e₁ e₂ .transf-eq x = P.pair-cong (e₁ .transf-eq x) (e₂ .transf-eq x)
products .HasProducts.pair-p₁ f g .transf-eq x = P.pair-p₁ _ _
products .HasProducts.pair-p₂ f g .transf-eq x = P.pair-p₂ _ _
products .HasProducts.pair-ext f .transf-eq x = P.pair-ext _
