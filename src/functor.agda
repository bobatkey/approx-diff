{-# OPTIONS --prop --postfix-projections --safe #-}

module functor {o₁ m₁ e₁ o₂ m₂ e₂} where

open import Level
open import categories

record Functor
         (𝒞 : Category o₁ m₁ e₁)
         (𝒟 : Category o₂ m₂ e₂) : Set (o₁ ⊔ o₂ ⊔ m₁ ⊔ m₂ ⊔ e₁ ⊔ e₂) where
  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
  field
    fobj : 𝒞.obj → 𝒟.obj
    fmor : ∀ {x y} → x 𝒞.⇒ y → fobj x 𝒟.⇒ fobj y
    fmor-cong : ∀ {x y}{f₁ f₂ : x 𝒞.⇒ y} → f₁ 𝒞.≈ f₂ → fmor f₁ 𝒟.≈ fmor f₂
    fmor-id : ∀ {x} → fmor (𝒞.id x) 𝒟.≈ 𝒟.id _
    fmor-comp : ∀ {x y z} (f : y 𝒞.⇒ z) (g : x 𝒞.⇒ y) →
                fmor (f 𝒞.∘ g) 𝒟.≈ (fmor f 𝒟.∘ fmor g)

-- FIXME: composition of functors, and the identity functor

record NatTrans
         {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂}
         (F G : Functor 𝒞 𝒟) : Set (o₁ ⊔ o₂ ⊔ m₁ ⊔ m₂ ⊔ e₁ ⊔ e₂) where
  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
  open Functor
  field
    transf : ∀ x → F .fobj x 𝒟.⇒ G .fobj x
    natural : ∀ {x y} (f : x 𝒞.⇒ y) →
      (G .fmor f 𝒟.∘ transf x) 𝒟.≈ (transf y 𝒟.∘ F .fmor f)



--
