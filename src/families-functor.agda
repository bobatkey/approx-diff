{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level
open import prop-setoid
  using (IsEquivalence; module ≈-Reasoning)
  renaming (≃m-isEquivalence to ≈s-isEquivalence; _⇒_ to _⇒s_)
open import categories
open import setoid-cat
open import functor
open import grothendieck
open import fam

module families-functor where

module _ {o₁ m₁ e₁ o₂ m₂ e₂}
         {𝒞 : Category o₁ m₁ e₁}
         {𝒟 : Category o₂ m₂ e₂}
         os es
         (F : Functor 𝒞 𝒟) where

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    module Fam𝒞 = CategoryOfFamilies os es 𝒞
    module Fam𝒟 = CategoryOfFamilies os es 𝒟

  open Fam
  open _⇒f_
  open _≃f_
  open IsEquivalence
  open CategoryOfFamilies.Obj
  open CategoryOfFamilies.Mor
  open CategoryOfFamilies._≃_
  open Functor

  FamF : Functor Fam𝒞.cat Fam𝒟.cat
  FamF .fobj X .idx = X .idx
  FamF .fobj X .fam = changeCat F (X .fam)
  FamF .fmor f .idxf = f .idxf
  FamF .fmor f .famf .transf x = F .fmor (f .famf .transf x)
  FamF .fmor {X} {Y} f .famf .natural x₁≈x₂ =
    begin
      F .fmor (f .famf .transf _) 𝒟.∘ F .fmor (X .fam .subst _)
    ≈⟨ 𝒟.≈-sym (F .fmor-comp _ _) ⟩
      F .fmor (f .famf .transf _ 𝒞.∘ X .fam .subst _)
    ≈⟨ F .fmor-cong (f .famf .natural _) ⟩
      F .fmor (Y .fam .subst _ 𝒞.∘ f .famf .transf _)
    ≈⟨ F .fmor-comp _ _ ⟩
      F .fmor (Y .fam .subst _) 𝒟.∘ F .fmor (f .famf .transf _)
    ∎ where open ≈-Reasoning 𝒟.isEquiv
  FamF .fmor-cong f₁≈f₂ .idxf-eq = f₁≈f₂ .idxf-eq
  FamF .fmor-cong {X} {Y} {f₁} {f₂} f₁≈f₂ .famf-eq .transf-eq {x} =
    begin
      F .fmor (Y .fam .subst _) 𝒟.∘ F .fmor (f₁ .famf .transf x)
    ≈˘⟨ F .fmor-comp _ _ ⟩
      F .fmor (Y .fam .subst _ 𝒞.∘ f₁ .famf .transf x)
    ≈⟨ F .fmor-cong (f₁≈f₂ .famf-eq .transf-eq) ⟩
      F .fmor (f₂ .famf .transf x)
    ∎
    where open ≈-Reasoning 𝒟.isEquiv
  FamF .fmor-id .idxf-eq = ≈s-isEquivalence .refl
  FamF .fmor-id {X} .famf-eq .transf-eq {x} =
    begin
      F .fmor (X .fam .subst _) 𝒟.∘ F .fmor (𝒞.id _)
    ≈⟨ 𝒟.∘-cong (F .fmor-cong (X .fam .refl*)) 𝒟.≈-refl ⟩
      F .fmor (𝒞.id _) 𝒟.∘ F .fmor (𝒞.id _)
    ≈⟨ 𝒟.∘-cong (F .fmor-id) (F .fmor-id) ⟩
      𝒟.id _ 𝒟.∘ 𝒟.id _
    ≈⟨ 𝒟.id-left ⟩
      𝒟.id _
    ∎
    where open ≈-Reasoning 𝒟.isEquiv
  FamF .fmor-comp f g .idxf-eq = ≈s-isEquivalence .refl
  FamF .fmor-comp {X} {Y} {Z} f g .famf-eq .transf-eq {x} =
    begin
      F .fmor (Z .fam .subst _) 𝒟.∘ F .fmor (𝒞.id _ 𝒞.∘ (f .famf .transf _ 𝒞.∘ g .famf .transf x))
    ≈⟨ 𝒟.∘-cong (F .fmor-cong (Z .fam .refl*)) (F .fmor-cong 𝒞.id-left) ⟩
      F .fmor (𝒞.id _) 𝒟.∘ F .fmor (f .famf .transf _ 𝒞.∘ g .famf .transf x)
    ≈⟨ 𝒟.∘-cong (F .fmor-id) (F .fmor-comp _ _) ⟩
      𝒟.id _ 𝒟.∘ (F .fmor (f .famf .transf _) 𝒟.∘ F .fmor (g .famf .transf x))
    ∎
    where open ≈-Reasoning 𝒟.isEquiv

module _ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂}
         os es (F G : Functor 𝒞 𝒟)
       where

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟

  open Functor
  open NatTrans
  open Fam
  open CategoryOfFamilies.Obj
  open CategoryOfFamilies.Mor
  open CategoryOfFamilies._≃_
  open _⇒f_
  open _≃f_

  FamNat : (α : NatTrans F G) → NatTrans (FamF os es F) (FamF os es G)
  FamNat α .transf X .idxf = prop-setoid.idS _
  FamNat α .transf X .famf .transf x = α .transf (X .fam .fm x)
  FamNat α .transf X .famf .natural h = 𝒟.≈-sym (α .natural (X .fam .subst h))
  FamNat α .natural f .idxf-eq = Category.id-swap' (SetoidCat _ _)
  FamNat α .natural {X} {Y} f .famf-eq .transf-eq {x} =
    begin
      G .fmor (Y .fam .subst _ ) 𝒟.∘ (𝒟.id _ 𝒟.∘ (G .fmor (f .famf .transf x) 𝒟.∘ α .transf (X .fam .fm x)))
    ≈⟨ 𝒟.∘-cong (G .fmor-cong (Y .fam .refl*)) 𝒟.id-left ⟩
      G .fmor (𝒞.id _) 𝒟.∘ (G .fmor (f .famf .transf x) 𝒟.∘ α .transf (X .fam .fm x))
    ≈⟨ 𝒟.∘-cong (G .fmor-id) (α .natural (f .famf .transf x)) ⟩
      𝒟.id _ 𝒟.∘ (α .transf (Y .fam .fm (f .idxf ._⇒s_.func x)) 𝒟.∘ F .fmor (f .famf .transf x))
    ∎
    where open ≈-Reasoning 𝒟.isEquiv
