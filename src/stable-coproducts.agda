{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_)
open import categories using (Category; HasCoproducts)

module stable-coproducts {o m e} {𝒞 : Category o m e} (𝒞CP : HasCoproducts 𝒞) where

private
  module 𝒞 = Category 𝒞
  module 𝒞CP = HasCoproducts 𝒞CP

open 𝒞.Iso

record StableBits {x₁ x₂ x y}
                  (f : 𝒞.Iso (𝒞CP .HasCoproducts.coprod x₁ x₂) x)
                  (g : y 𝒞.⇒ x) : Set (o ⊔ m ⊔ e) where
  field
    y₁  : 𝒞.obj
    y₂  : 𝒞.obj
    h₁  : y₁ 𝒞.⇒ x₁
    h₂  : y₂ 𝒞.⇒ x₂
    h   : 𝒞.Iso (𝒞CP.coprod y₁ y₂) y
    eq₁ : (f .fwd 𝒞.∘ (𝒞CP.in₁ 𝒞.∘ h₁)) 𝒞.≈ (g 𝒞.∘ (h .fwd 𝒞.∘ 𝒞CP.in₁))
    eq₂ : (f .fwd 𝒞.∘ (𝒞CP.in₂ 𝒞.∘ h₂)) 𝒞.≈ (g 𝒞.∘ (h .fwd 𝒞.∘ 𝒞CP.in₂))

Stable : Set (o ⊔ m ⊔ e)
Stable = ∀ {x₁ x₂ x y} f g → StableBits {x₁} {x₂} {x} {y} f g
