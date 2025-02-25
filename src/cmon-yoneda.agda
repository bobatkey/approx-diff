{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_; lift; lower)
open import prop using (lift; lower)
open import prop-setoid using (IsEquivalence; idS; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
open import categories using (Category; opposite; IsProduct)
open import functor using ([_⇒_]; Functor; NatTrans; ≃-NatTrans)
open import commutative-monoid using (CommutativeMonoid; _=[_]>_)
open import cmon-enriched using (CMonEnriched; module cmon+products→biproducts)
open import commutative-monoid-cat using (_⇒_; toSetoid)
  renaming (cat to CMon; Obj to CMonObj)

module cmon-yoneda {o m e} os es (𝒞 : Category o m e) (CM𝒞 : CMonEnriched 𝒞) where

import yoneda os es 𝒞 as yoneda

PSh = [ opposite 𝒞 ⇒ CMon (m ⊔ os) (e ⊔ es) ]

private
  module 𝒞 = Category 𝒞
open _⇒_
open _=[_]>_
open CommutativeMonoid
open CMonObj
open Functor
open NatTrans
open ≃-NatTrans

open CMonEnriched CM𝒞

よ₀ : 𝒞.obj → PSh .Category.obj
よ₀ x .fobj y .carrier = yoneda.よ₀ x .fobj y
よ₀ x .fobj y .commMonoid .ε = lift εm
よ₀ x .fobj y .commMonoid ._+_ (lift f) (lift g) = lift (f +m g)
よ₀ x .fobj y .commMonoid .+-cong (lift e₁) (lift e₂) = lift (homCM _ _ .+-cong e₁ e₂)
よ₀ x .fobj y .commMonoid .+-lunit = lift (homCM _ _ .+-lunit)
よ₀ x .fobj y .commMonoid .+-assoc = lift (homCM _ _ .+-assoc)
よ₀ x .fobj y .commMonoid .+-comm = lift (homCM _ _ .+-comm)
よ₀ x .fmor f .function = yoneda.よ₀ x .fmor f
よ₀ x .fmor f .cmFunc .preserve-ε = lift (comp-bilinear-ε₁ _)
よ₀ x .fmor f .cmFunc .preserve-+ = lift (comp-bilinear₁ _ _ _)
よ₀ x .fmor-cong = yoneda.よ₀ x .fmor-cong
よ₀ x .fmor-id = yoneda.よ₀ x .fmor-id
よ₀ x .fmor-comp = yoneda.よ₀ x .fmor-comp

よ : Functor 𝒞 PSh
よ .fobj = よ₀
よ .fmor f .transf y .function = yoneda.よ .fmor f .transf y
よ .fmor f .transf y .cmFunc .preserve-ε = lift (comp-bilinear-ε₂ _)
よ .fmor f .transf y .cmFunc .preserve-+ = lift (comp-bilinear₂ _ _ _)
よ .fmor f .natural = yoneda.よ .fmor f .natural
よ .fmor-cong f₁≈f₂ .transf-eq = yoneda.よ .fmor-cong f₁≈f₂ .transf-eq
よ .fmor-id .transf-eq = yoneda.よ .fmor-id .transf-eq
よ .fmor-comp f g .transf-eq = yoneda.よ .fmor-comp _ _ .transf-eq

------------------------------------------------------------------------------
-- TODO: Yoneda lemma

------------------------------------------------------------------------------
-- よ preserves products
module _ (x y p : 𝒞.obj) (p₁ : p 𝒞.⇒ x) (p₂ : p 𝒞.⇒ y)
         (p-isproduct : IsProduct 𝒞 x y p p₁ p₂) where

  open _⇒s_
  open _≈s_

  open IsProduct p-isproduct
  open cmon+products→biproducts CM𝒞 (record { isProduct = p-isproduct })
    using (pair-ε; pair-+)

  preserve-products : IsProduct PSh (よ₀ x) (よ₀ y) (よ₀ p) (よ .fmor p₁) (よ .fmor p₂)
  preserve-products .pair {Z} f g .transf z .function .func Zz .lower =
    pair (f .transf z .func Zz .lower) (g .transf z .func Zz .lower)
  preserve-products .pair {Z} f g .transf z .function .func-resp-≈ {Zz₁} {Zz₂} Zz₁≈Zz₂ .lower =
    pair-cong (f .transf z .func-resp-≈ Zz₁≈Zz₂ .lower) (g .transf z .func-resp-≈ Zz₁≈Zz₂ .lower)
  preserve-products .pair {Z} f g .transf z .cmFunc .preserve-ε .lower =
    begin
      pair (f .transf z .func (Z .fobj z .ε) .lower) (g .transf z .func (Z .fobj z .ε) .lower)
    ≈⟨ pair-cong (f .transf z .preserve-ε .lower) (g .transf z .preserve-ε .lower) ⟩
      pair εm εm
    ≈⟨ pair-ε ⟩
      εm
    ∎ where open ≈-Reasoning 𝒞.isEquiv
  preserve-products .pair {Z} f g .transf z .cmFunc .preserve-+ {a} {b} .lower =
    begin
      pair (f .transf z .func (Z .fobj z ._+_ a b) .lower) (g .transf z .func (Z .fobj z ._+_ a b) .lower)
    ≈⟨ pair-cong (f .transf z .preserve-+ .lower) (g .transf z .preserve-+ .lower) ⟩
      pair (f .transf z .func a .lower +m f .transf z .func b .lower) (g .transf z .func a .lower +m g .transf z .func b .lower)
    ≈˘⟨ pair-+ _ _ _ _ ⟩
      pair (f .transf z .func a .lower) (g .transf z .func a .lower) +m pair (f .transf z .func b .lower) (g .transf z .func b .lower)
    ∎ where open ≈-Reasoning 𝒞.isEquiv
  preserve-products .pair {Z} f g .natural {x₁} {y₁} h .func-eq {Zz₁} {Zz₂} e .lower =
    begin
      pair (f .transf x₁ .func Zz₁ .lower) (g .transf x₁ .func Zz₁ .lower) 𝒞.∘ h
    ≈⟨ pair-natural _ _ _ ⟩
      pair (f .transf x₁ .func Zz₁ .lower 𝒞.∘ h) (g .transf x₁ .func Zz₁ .lower 𝒞.∘ h)
    ≈⟨ pair-cong (f .natural h .func-eq e .lower) (g .natural h .func-eq e .lower) ⟩
      pair (f .transf y₁ .func (Z .fmor h .func Zz₂) .lower) (g .transf y₁ .func (Z .fmor h .func Zz₂) .lower)
    ∎ where open ≈-Reasoning 𝒞.isEquiv
  preserve-products .pair-cong {Z} f₁≈f₂ g₁≈g₂ .transf-eq w .func-eq e .lower =
    pair-cong (f₁≈f₂ .transf-eq w .func-eq e .lower) (g₁≈g₂ .transf-eq w .func-eq e .lower)
  preserve-products .pair-p₁ {Z} f g .transf-eq w .func-eq {Zw₁} {Zw₂} e .lower =
    begin
      p₁ 𝒞.∘ pair (f .transf w .func Zw₁ .lower) (g .transf w .func Zw₁ .lower)
    ≈⟨ pair-p₁ _ _ ⟩
      f .transf w .func Zw₁ .lower
    ≈⟨ f .transf w .func-resp-≈ e .lower ⟩
      f .transf w .func Zw₂ .lower
    ∎ where open ≈-Reasoning 𝒞.isEquiv
  preserve-products .pair-p₂ {Z} f g .transf-eq w .func-eq {Zw₁} {Zw₂} e .lower =
    begin
      p₂ 𝒞.∘ pair (f .transf w .func Zw₁ .lower) (g .transf w .func Zw₁ .lower)
    ≈⟨ pair-p₂ _ _ ⟩
      g .transf w .func Zw₁ .lower
    ≈⟨ g .transf w .func-resp-≈ e .lower ⟩
      g .transf w .func Zw₂ .lower
    ∎ where open ≈-Reasoning 𝒞.isEquiv
  preserve-products .pair-ext {Z} f .transf-eq w .func-eq {Zw₁} {Zw₂} e .lower =
    begin
      pair (p₁ 𝒞.∘ f .transf w .func Zw₁ .lower) (p₂ 𝒞.∘ f .transf w .func Zw₁ .lower)
    ≈⟨ pair-ext _ ⟩
      f .transf w .func Zw₁ .lower
    ≈⟨ f .transf w .func-resp-≈ e .lower ⟩
      f .transf w .func Zw₂ .lower
    ∎ where open ≈-Reasoning 𝒞.isEquiv
