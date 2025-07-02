{-# OPTIONS --postfix-projections --prop --safe #-}

open import categories using (Category; HasTerminal; HasProducts; HasCoproducts; HasExponentials; HasBooleans; coproducts+exp→booleans)
open import functor using (Functor)
open import finite-product-functor
  using (preserve-chosen-products; module preserve-chosen-products-consequences)
open import finite-coproduct-functor
  using (preserve-chosen-coproducts; module preserve-chosen-coproducts-consequences)

open import language-syntax using (module language)
open import signature

open Functor

module language-fo-interpretation {ℓ} (Sig : Signature ℓ) where

open language Sig

module interp
  {o m e} (𝒞 : Category o m e) (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞CP : HasCoproducts 𝒞)
  (Int : Model PFPC[ 𝒞 , 𝒞T , 𝒞P , 𝒞CP .HasCoproducts.coprod (𝒞T .HasTerminal.witness) (𝒞T .HasTerminal.witness) ] Sig)
  where

  open Category 𝒞
  open HasTerminal 𝒞T renaming (witness to 𝟙)
  open HasProducts 𝒞P renaming (prod to _×_)
  open HasCoproducts 𝒞CP renaming (coprod to _+_)

  ⟦_⟧ty : ∀ {τ} → first-order τ → obj
  ⟦ unit ⟧ty = 𝟙
  ⟦ bool ⟧ty = 𝟙 + 𝟙
  ⟦ base s ⟧ty = Int .Model.⟦sort⟧ s
  ⟦ τ₁ [×] τ₂ ⟧ty = ⟦ τ₁ ⟧ty × ⟦ τ₂ ⟧ty

  ⟦_⟧ctxt : ∀ {Γ} → first-order-ctxt Γ → obj
  ⟦ emp ⟧ctxt = 𝟙
  ⟦ Γ , τ ⟧ctxt = ⟦ Γ ⟧ctxt × ⟦ τ ⟧ty

module interp-preserved
  {o₁ m₁ e₁ o₂ m₂ e₂}
  (𝒞 : Category o₁ m₁ e₁) (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞CP : HasCoproducts 𝒞)
  (𝒟 : Category o₂ m₂ e₂) (𝒟T : HasTerminal 𝒟) (𝒟P : HasProducts 𝒟) (𝒟CP : HasCoproducts 𝒟) (𝒟E : HasExponentials 𝒟 𝒟P)
  (F : Functor 𝒞 𝒟)
  (FT : Category.IsIso 𝒟 (HasTerminal.to-terminal 𝒟T {F .fobj (𝒞T .HasTerminal.witness)}))
  (FP : preserve-chosen-products F 𝒞P 𝒟P)
  (FC : preserve-chosen-coproducts F 𝒞CP 𝒟CP)
  (Int : Model PFPC[ 𝒞 , 𝒞T , 𝒞P , 𝒞CP .HasCoproducts.coprod (𝒞T .HasTerminal.witness) (𝒞T .HasTerminal.witness) ] Sig)
  where

  private
    module 𝒟 = Category 𝒟
    module 𝒟P = HasProducts 𝒟P

  open interp 𝒞 𝒞T 𝒞P 𝒞CP Int renaming (⟦_⟧ty to 𝒞⟦_⟧ty; ⟦_⟧ctxt to 𝒞⟦_⟧ctxt) using ()
  open import language-interpretation Sig 𝒟 𝒟T 𝒟P 𝒟CP 𝒟E
     (transport-model Sig F {!!} {!!} Int)
    renaming (⟦_⟧ty to 𝒟⟦_⟧ty; ⟦_⟧ctxt to 𝒟⟦_⟧ctxt) using ()

  ⟦_⟧-iso : ∀ {τ} (τ-fo : first-order τ) → 𝒟.Iso (F .fobj 𝒞⟦ τ-fo ⟧ty) 𝒟⟦ τ ⟧ty
  ⟦ unit ⟧-iso = 𝒟.IsIso→Iso FT
  ⟦ bool ⟧-iso = 𝒟.Iso-trans (𝒟.Iso-sym (𝒟.IsIso→Iso FC)) {!!}
  ⟦ base s ⟧-iso = 𝒟.Iso-refl
  ⟦ τ₁ [×] τ₂ ⟧-iso = 𝒟.Iso-trans (𝒟.IsIso→Iso FP) (𝒟P.product-preserves-iso ⟦ τ₁ ⟧-iso ⟦ τ₂ ⟧-iso)
