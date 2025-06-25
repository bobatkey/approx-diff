{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (suc; _⊔_)
open import Data.Product using (_,_)
open import prop using (_,_)
open import prop-setoid using (_∘S_; idS; module ≈-Reasoning) renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
open import categories using (Category; HasProducts)
open import functor using (Functor)
open import setoid-cat using (SetoidCat; Setoid-products)

module sconing {o m e} (𝒞 : Category o m e) (P : HasProducts 𝒞) (Probe : Category.obj 𝒞) where

-- Given a category with finite products, and a fixed object P, the
-- functor 𝒞(P, -) : 𝒞 ⇒ SetoidCat o e preserves finite products.

open Functor
open _⇒s_
open _≈s_
private
  module 𝒞 = Category 𝒞
  module P = HasProducts P
  module 𝒟P = HasProducts (Setoid-products m e)

Scone : Functor 𝒞 (SetoidCat m e)
Scone .fobj x = 𝒞.hom-setoid Probe x
Scone .fmor f .func g = f 𝒞.∘ g
Scone .fmor f .func-resp-≈ g₁≈g₂ = 𝒞.∘-cong 𝒞.≈-refl g₁≈g₂
Scone .fmor-cong f₁≈f₂ .func-eq g₁≈g₂ = 𝒞.∘-cong f₁≈f₂ g₁≈g₂
Scone .fmor-id .func-eq f₁≈f₂ = 𝒞.≈-trans 𝒞.id-left f₁≈f₂
Scone .fmor-comp f g .func-eq h₁≈h₂ = 𝒞.≈-trans (𝒞.∘-cong 𝒞.≈-refl h₁≈h₂) (𝒞.assoc _ _ _)

------------------------------------------------------------------------------
-- Support for products

mul : ∀ {x y} → 𝒟P.prod (Scone .fobj x) (Scone .fobj y) ⇒s Scone .fobj (P.prod x y)
mul .func (f , g) = P.pair f g
mul .func-resp-≈ (f₁≈f₂ , g₁≈g₂) = P.pair-cong f₁≈f₂ g₁≈g₂

mul⁻¹ : ∀ {x y} → Scone .fobj (P.prod x y) ⇒s 𝒟P.prod (Scone .fobj x) (Scone .fobj y)
mul⁻¹ .func f = (P.p₁ 𝒞.∘ f) , (P.p₂ 𝒞.∘ f)
mul⁻¹ .func-resp-≈ f₁≈f₂ = (𝒞.∘-cong 𝒞.≈-refl f₁≈f₂) , (𝒞.∘-cong 𝒞.≈-refl f₁≈f₂)

mul-inv : ∀ {x y} → (mul {x} {y} ∘S mul⁻¹) ≈s idS _
mul-inv .func-eq f₁≈f₂ = 𝒞.≈-trans (P.pair-ext _) f₁≈f₂

mul-natural : ∀ {x x' y y'} {f : x 𝒞.⇒ x'} {g : y 𝒞.⇒ y'} →
              (Scone .fmor (P.prod-m f g) ∘S mul) ≈s (mul ∘S 𝒟P.prod-m (Scone .fmor f) (Scone .fmor g))
mul-natural {x}{x'}{y}{y'}{f = f} {g = g} .func-eq {h₁ , h₁'}{h₂ , h₂'} (h₁≈h₂ , h₁'≈h₂') = begin
    P.pair (f 𝒞.∘ P.p₁) (g 𝒞.∘ P.p₂) 𝒞.∘ P.pair h₁ h₁'
  ≈⟨ P.pair-compose _ _ _ _ ⟩
    P.pair (f 𝒞.∘ h₁) (g 𝒞.∘ h₁')
  ≈⟨ P.pair-cong (𝒞.∘-cong 𝒞.≈-refl h₁≈h₂) (𝒞.∘-cong 𝒞.≈-refl h₁'≈h₂') ⟩
    P.pair (f 𝒞.∘ h₂) (g 𝒞.∘ h₂')
  ∎
  where open ≈-Reasoning 𝒞.isEquiv

Scone-p₁ : ∀ {x y} → (Scone .fmor (P.p₁ {x} {y}) ∘S mul) ≈s 𝒟P.p₁
Scone-p₁ .func-eq {f₁ , f₁'}{f₂ , f₂'} (f₁≈f₂ , f₁'≈f₂') =
  𝒞.≈-trans (P.pair-p₁ _ _) f₁≈f₂

------------------------------------------------------------------------------
-- Support for coproducts
