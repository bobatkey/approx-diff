{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_; 0ℓ)
open import prop-setoid using (module ≈-Reasoning)
open import categories using (Category; HasCoproducts)
open import functor using (Functor)

module finite-coproduct-functor
  {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂}
  (F : Functor 𝒞 𝒟)
  where

private
  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟
  module F = Functor F

-- FIXME: do preservation of coproducts as in finite-product-functor

module _ (𝒞P : HasCoproducts 𝒞) (𝒟P : HasCoproducts 𝒟) where

  private
    module 𝒞P = HasCoproducts 𝒞P
    module 𝒟P = HasCoproducts 𝒟P

  preserve-chosen-coproducts : Set (o₁ ⊔ m₂ ⊔ e₂)
  preserve-chosen-coproducts = ∀ {x y} → 𝒟.IsIso (𝒟P.copair (F.fmor (𝒞P.in₁ {x} {y})) (F.fmor (𝒞P.in₂ {x} {y})))

  module preserve-chosen-coproducts-consequences (Fp : preserve-chosen-coproducts) where

    mul : ∀ {x y} → F.fobj (𝒞P.coprod x y) 𝒟.⇒ 𝒟P.coprod (F.fobj x) (F.fobj y)
    mul = Fp .𝒟.IsIso.inverse

    mul⁻¹ : ∀ {x y} →  𝒟P.coprod (F.fobj x) (F.fobj y) 𝒟.⇒ F.fobj (𝒞P.coprod x y)
    mul⁻¹ = 𝒟P.copair (F.fmor 𝒞P.in₁) (F.fmor 𝒞P.in₂)

    mul-inv : ∀ {x y} → (mul {x} {y} 𝒟.∘ mul⁻¹) 𝒟.≈ 𝒟.id _
    mul-inv = Category.IsIso.inverse∘f≈id Fp

    -- FIXME: naturality

    F-in₁ : ∀ {x y} → (mul 𝒟.∘ F.fmor (𝒞P.in₁ {x} {y})) 𝒟.≈ 𝒟P.in₁
    F-in₁ {x} {y} = begin
        mul 𝒟.∘ F.fmor (𝒞P.in₁ {x} {y})
      ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟P.copair-in₁ _ _) ⟩
        mul 𝒟.∘ (mul⁻¹ 𝒟.∘ 𝒟P.in₁)
      ≈˘⟨ 𝒟.assoc _ _ _ ⟩
        (mul 𝒟.∘ mul⁻¹) 𝒟.∘ 𝒟P.in₁
      ≈⟨ 𝒟.∘-cong (Category.IsIso.inverse∘f≈id Fp) 𝒟.≈-refl ⟩
        𝒟.id _ 𝒟.∘ 𝒟P.in₁
      ≈⟨ 𝒟.id-left ⟩
        𝒟P.in₁
      ∎
      where open ≈-Reasoning 𝒟.isEquiv

    F-in₂ : ∀ {x y} → (mul 𝒟.∘ F.fmor (𝒞P.in₂ {x} {y})) 𝒟.≈ 𝒟P.in₂
    F-in₂ {x} {y} = begin
        mul 𝒟.∘ F.fmor (𝒞P.in₂ {x} {y})
      ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟P.copair-in₂ _ _) ⟩
        mul 𝒟.∘ (mul⁻¹ 𝒟.∘ 𝒟P.in₂)
      ≈˘⟨ 𝒟.assoc _ _ _ ⟩
        (mul 𝒟.∘ mul⁻¹) 𝒟.∘ 𝒟P.in₂
      ≈⟨ 𝒟.∘-cong (Category.IsIso.inverse∘f≈id Fp) 𝒟.≈-refl ⟩
        𝒟.id _ 𝒟.∘ 𝒟P.in₂
      ≈⟨ 𝒟.id-left ⟩
        𝒟P.in₂
      ∎
      where open ≈-Reasoning 𝒟.isEquiv

    F-copair : ∀ {x y z} {f₁ : x 𝒞.⇒ z} {f₂ : y 𝒞.⇒ z} →
               (𝒟P.copair (F.fmor f₁) (F.fmor f₂) 𝒟.∘ mul) 𝒟.≈ F.fmor (𝒞P.copair f₁ f₂)
    F-copair {x} {y} {z} {f₁} {f₂} = begin
         𝒟P.copair (F.fmor f₁) (F.fmor f₂) 𝒟.∘ mul
       ≈˘⟨ 𝒟.∘-cong (𝒟P.copair-cong (F.fmor-cong (𝒞P.copair-in₁ _ _)) (F.fmor-cong (𝒞P.copair-in₂ _ _))) 𝒟.≈-refl ⟩
         𝒟P.copair (F.fmor (𝒞P.copair f₁ f₂ 𝒞.∘ 𝒞P.in₁)) (F.fmor (𝒞P.copair f₁ f₂ 𝒞.∘ 𝒞P.in₂)) 𝒟.∘ mul
       ≈⟨ 𝒟.∘-cong (𝒟P.copair-cong (F.fmor-comp _ _) (F.fmor-comp _ _)) 𝒟.≈-refl ⟩
         𝒟P.copair (F.fmor (𝒞P.copair f₁ f₂) 𝒟.∘ F.fmor 𝒞P.in₁) (F.fmor (𝒞P.copair f₁ f₂) 𝒟.∘ F.fmor 𝒞P.in₂) 𝒟.∘ mul
       ≈˘⟨ 𝒟.∘-cong (𝒟P.copair-natural _ _ _) 𝒟.≈-refl ⟩
         (F.fmor (𝒞P.copair f₁ f₂) 𝒟.∘ 𝒟P.copair (F.fmor 𝒞P.in₁) (F.fmor 𝒞P.in₂)) 𝒟.∘ mul
       ≡⟨⟩
         (F.fmor (𝒞P.copair f₁ f₂) 𝒟.∘ mul⁻¹) 𝒟.∘ mul
       ≈⟨ 𝒟.assoc _ _ _ ⟩
         F.fmor (𝒞P.copair f₁ f₂) 𝒟.∘ (mul⁻¹ 𝒟.∘ mul)
       ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (Category.IsIso.f∘inverse≈id Fp) ⟩
         F.fmor (𝒞P.copair f₁ f₂) 𝒟.∘ 𝒟.id _
       ≈⟨ 𝒟.id-right ⟩
         F.fmor (𝒞P.copair f₁ f₂)
       ∎
       where open ≈-Reasoning 𝒟.isEquiv
