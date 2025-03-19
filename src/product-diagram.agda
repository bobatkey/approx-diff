{-# OPTIONS --prop --postfix-projections --safe #-}

module product-diagram where

open import Level using (0ℓ)
open import prop using (⊤; tt)
open import prop-setoid using (IsEquivalence; module ≈-Reasoning)
open import categories using (Category; IsProduct)
open import functor using (Functor; NatTrans; NatIso; IsLimit; ≃-NatTrans; constFmor; constF)

data Obj : Set where
  L R : Obj

data _⇒_ : Obj → Obj → Set where
  id : ∀ {x} → x ⇒ x

open IsEquivalence

cat : Category 0ℓ 0ℓ 0ℓ
cat .Category.obj = Obj
cat .Category._⇒_ = _⇒_
cat .Category._≈_ _ _ = ⊤
cat .Category.isEquiv .refl = tt
cat .Category.isEquiv .sym tt = tt
cat .Category.isEquiv .trans tt tt = tt
cat .Category.id x = id
cat .Category._∘_ id id = id
cat .Category.∘-cong _ _ = tt
cat .Category.id-left = tt
cat .Category.id-right = tt
cat .Category.assoc f g h = tt

module _ {o m e} (𝒞 : Category o m e) where

  private
    module 𝒞 = Category 𝒞

  open IsProduct
  open IsLimit
  open Functor
  open NatTrans
  open ≃-NatTrans

  pair→functor : 𝒞.obj → 𝒞.obj → Functor cat 𝒞
  pair→functor x y .fobj L = x
  pair→functor x y .fobj R = y
  pair→functor x y .fmor id = 𝒞.id _
  pair→functor x y .fmor-cong {f₁ = id} {id} tt = 𝒞.≈-refl
  pair→functor x y .fmor-id = 𝒞.≈-refl
  pair→functor x y .fmor-comp id id = 𝒞.≈-sym 𝒞.id-left

  span→cone : ∀ {F : Functor cat 𝒞} {z} → z 𝒞.⇒ F .fobj L → z 𝒞.⇒ F .fobj R →
                 NatTrans (constF cat z) F
  span→cone f g .transf L = f
  span→cone f g .transf R = g
  span→cone {F} {z} f g .natural {x} {x} id = begin
      F .fmor id 𝒞.∘ span→cone {F} f g .transf x
    ≈⟨ 𝒞.∘-cong (F .fmor-id) 𝒞.≈-refl ⟩
      𝒞.id _ 𝒞.∘ span→cone {F} f g .transf x
    ≈⟨ 𝒞.id-swap ⟩
      span→cone {F} f g .transf x 𝒞.∘ 𝒞.id _
    ∎
    where open ≈-Reasoning 𝒞.isEquiv

  span→cone-cong : ∀ {F : Functor cat 𝒞} {z}
                   {f₁ f₂ : z 𝒞.⇒ F .fobj L}
                   {g₁ g₂ : z 𝒞.⇒ F .fobj R} →
                   f₁ 𝒞.≈ f₂ → g₁ 𝒞.≈ g₂ →
                   ≃-NatTrans (span→cone {F} f₁ g₁) (span→cone {F} f₂ g₂)
  span→cone-cong f₁≈f₂ g₂≈g₂ .transf-eq L = f₁≈f₂
  span→cone-cong f₁≈f₂ g₂≈g₂ .transf-eq R = g₂≈g₂

  span→cone-ext : ∀ {F : Functor cat 𝒞} {x y} {f : x 𝒞.⇒ y} {α : NatTrans (constF cat y) F} →
                  ≃-NatTrans (span→cone (α .transf L 𝒞.∘ f) (α .transf R 𝒞.∘ f)) (α functor.∘ constFmor f)
  span→cone-ext .transf-eq L = 𝒞.≈-refl
  span→cone-ext .transf-eq R = 𝒞.≈-refl

  limit→product : ∀ {F : Functor cat 𝒞} {p} {cone} →
                  IsLimit F p cone →
                  IsProduct 𝒞 (F .fobj L) (F .fobj R) p (cone .transf L) (cone .transf R)
  limit→product is-limit .pair {z} f g = is-limit .lambda z (span→cone f g)
  limit→product is-limit .pair-cong f₁≈f₂ g₁≈g₂ = is-limit .lambda-cong (span→cone-cong f₁≈f₂ g₁≈g₂)
  limit→product is-limit .pair-p₁ f g = is-limit .lambda-eval _ .transf-eq L
  limit→product is-limit .pair-p₂ f g = is-limit .lambda-eval _ .transf-eq R
  limit→product {F} {p} {cone} is-limit .pair-ext {z} f = begin
      is-limit .lambda z (span→cone (cone .transf L 𝒞.∘ f) (cone .transf R 𝒞.∘ f))
    ≈⟨ is-limit .lambda-cong span→cone-ext ⟩
      is-limit .lambda z (cone functor.∘ constFmor f)
    ≈⟨ is-limit .lambda-ext _  ⟩
      f
    ∎
    where open ≈-Reasoning 𝒞.isEquiv

  product→limit : ∀ {x y p p₁ p₂} →
                  IsProduct 𝒞 x y p p₁ p₂ →
                  IsLimit (pair→functor x y) p (span→cone p₁ p₂)
  product→limit is-product .lambda z α = is-product .pair (α .transf L) (α .transf R)
  product→limit is-product .lambda-cong α≃β = is-product .pair-cong (α≃β .transf-eq L) (α≃β .transf-eq R)
  product→limit is-product .lambda-eval α .transf-eq L = is-product .pair-p₁ _ _
  product→limit is-product .lambda-eval α .transf-eq R = is-product .pair-p₂ _ _
  product→limit is-product .lambda-ext f = is-product .pair-ext f
