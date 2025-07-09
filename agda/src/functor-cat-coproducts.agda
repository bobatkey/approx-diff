{-# OPTIONS --prop --postfix-projections --safe #-}

open import prop-setoid using (module ≈-Reasoning)
open import categories using (Category; HasCoproducts)
open import functor using (Functor; NatTrans; ≃-NatTrans; [_⇒_])

module functor-cat-coproducts
    {o₁ m₁ e₁ o₂ m₂ e₂} (𝒞 : Category o₁ m₁ e₁) (𝒟 : Category o₂ m₂ e₂) (CP  : HasCoproducts 𝒟)
  where

open Functor
open NatTrans
open ≃-NatTrans

private
  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟
  module CP = HasCoproducts CP

_+_ : Functor 𝒞 𝒟 → Functor 𝒞 𝒟 → Functor 𝒞 𝒟
(F + G) .fobj x = CP.coprod (F .fobj x) (G .fobj x)
(F + G) .fmor f = CP.coprod-m (F .fmor f) (G .fmor f)
(F + G) .fmor-cong f₁≈f₂ = CP.coprod-m-cong (F .fmor-cong f₁≈f₂) (G .fmor-cong f₁≈f₂)
(F + G) .fmor-id {x} = begin
    CP.coprod-m (F .fmor (𝒞.id x)) (G .fmor (𝒞.id x))
  ≈⟨ CP.coprod-m-cong (F .fmor-id) (G .fmor-id) ⟩
    CP.coprod-m (𝒟.id _) (𝒟.id _)
  ≈⟨ CP.coprod-m-id ⟩
    𝒟.id (CP.coprod (F .fobj x) (G .fobj x))
  ∎
  where open ≈-Reasoning 𝒟.isEquiv
(F + G) .fmor-comp f g = begin
    CP.coprod-m (F .fmor (f 𝒞.∘ g)) (G .fmor (f 𝒞.∘ g))
  ≈⟨ CP.coprod-m-cong (F .fmor-comp f g) (G .fmor-comp f g) ⟩
    CP.coprod-m (F .fmor f 𝒟.∘ F .fmor g) (G .fmor f 𝒟.∘ G .fmor g)
  ≈⟨ CP.coprod-m-comp _ _ _ _ ⟩
    CP.coprod-m (F .fmor f) (G .fmor f) 𝒟.∘ CP.coprod-m (F .fmor g) (G .fmor g)
  ∎
  where open ≈-Reasoning 𝒟.isEquiv

+-in₁ : ∀ {F G} → NatTrans F (F + G)
+-in₁ .transf x = CP.in₁
+-in₁ .natural f = CP.copair-in₁ _ _

+-in₂ : ∀ {F G} → NatTrans G (F + G)
+-in₂ .transf x = CP.in₂
+-in₂ .natural f = CP.copair-in₂ _ _

+-copair : ∀ {F G H} → NatTrans F H → NatTrans G H → NatTrans (F + G) H
+-copair α β .transf x = CP.copair (α .transf x) (β .transf x)
+-copair {F} {G} {H} α β .natural {x} {y} f = begin
    H .fmor f 𝒟.∘ CP.copair (α .transf x) (β .transf x)
  ≈⟨ CP.copair-natural _ _ _ ⟩
    CP.copair (H .fmor f 𝒟.∘ α .transf x) (H .fmor f 𝒟.∘ β .transf x)
  ≈⟨ CP.copair-cong (α .natural f) (β .natural f) ⟩
    CP.copair (α .transf y 𝒟.∘ F .fmor f) (β .transf y 𝒟.∘ G .fmor f)
  ≈⟨ CP.copair-coprod _ _ _ _ ⟩
    CP.copair (α .transf y) (β .transf y) 𝒟.∘ CP.coprod-m (F .fmor f) (G .fmor f)
  ∎
  where open ≈-Reasoning 𝒟.isEquiv

open HasCoproducts

coproducts : HasCoproducts [ 𝒞 ⇒ 𝒟 ]
coproducts .coprod = _+_
coproducts .in₁ = +-in₁
coproducts .in₂ = +-in₂
coproducts .copair = +-copair
coproducts .copair-cong α₁≃α₂ β₁≃β₂ .transf-eq x = CP.copair-cong (α₁≃α₂ .transf-eq x) (β₁≃β₂ .transf-eq x)
coproducts .copair-in₁ α β .transf-eq x = CP.copair-in₁ (α .transf x) (β .transf x)
coproducts .copair-in₂ α β .transf-eq x = CP.copair-in₂ (α .transf x) (β .transf x)
coproducts .copair-ext α .transf-eq x = CP.copair-ext (α .transf x)
