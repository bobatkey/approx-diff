{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_; 0ℓ)
open import prop-setoid using (module ≈-Reasoning)
open import categories using (Category; IsTerminal; IsProduct; IsProduct-cong; HasProducts)
open import functor using (Functor; preserve-limits-of-shape; IsLimit;
                           NatIso; NatTrans; ≃-NatTrans; constFmor)

module finite-product-functor
  {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂}
  (F : Functor 𝒞 𝒟)
  where

private
  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟
  module F = Functor F

record FPFunctor : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  field
    preserve-terminal : ∀ t → IsTerminal 𝒞 t → IsTerminal 𝒟 (F.fobj t)
    preserve-products : ∀ (x y xy : 𝒞.obj)
      (p₁ : xy 𝒞.⇒ x) (p₂ : xy 𝒞.⇒ y) →
      IsProduct 𝒞 x y xy p₁ p₂ →
      IsProduct 𝒟 (F.fobj x) (F.fobj y) (F.fobj xy) (F.fmor p₁) (F.fmor p₂)

-- If a functor preserves the empty diagram, then it preserves terminal objects

open import empty-diagram using (IsLimit→IsTerminal; terminal→limit)
open import product-diagram using (IsLimit→IsProduct; product→limit)

mk-preserve-terminal : preserve-limits-of-shape empty-diagram.cat F →
                       ∀ t → IsTerminal 𝒞 t → IsTerminal 𝒟 (F.fobj t)
mk-preserve-terminal F-preserve t t-terminal =
    IsLimit→IsTerminal 𝒟 (F-preserve _ t _ (terminal→limit 𝒞 t-terminal))

-- If a functor preserves product-shaped limits, then it preserves products

mk-preserve-products : preserve-limits-of-shape product-diagram.cat F →
                       ∀ (x y xy : 𝒞.obj) (p₁ : xy 𝒞.⇒ x) (p₂ : xy 𝒞.⇒ y) →
                       IsProduct 𝒞 x y xy p₁ p₂ →
                       IsProduct 𝒟 (F.fobj x) (F.fobj y) (F.fobj xy) (F.fmor p₁) (F.fmor p₂)
mk-preserve-products F-preserve x y xy p₁ p₂ is-product =
  IsProduct-cong 𝒟 (𝒟.≈-trans 𝒟.id-right 𝒟.id-left) (𝒟.≈-trans 𝒟.id-right 𝒟.id-left) (IsLimit→IsProduct 𝒟 lim)
  where lim = F-preserve _ xy _ (product→limit 𝒞 is-product)

preserve-fp→FPFunctor : preserve-limits-of-shape empty-diagram.cat F →
                        preserve-limits-of-shape product-diagram.cat F →
                        FPFunctor
preserve-fp→FPFunctor preserve-empty preserve-product .FPFunctor.preserve-terminal = mk-preserve-terminal preserve-empty
preserve-fp→FPFunctor preserve-empty preserve-product .FPFunctor.preserve-products = mk-preserve-products preserve-product

continuous→FPFunctor : (∀ (𝒮 : Category 0ℓ 0ℓ 0ℓ) → preserve-limits-of-shape 𝒮 F) →
                       FPFunctor
continuous→FPFunctor preserve-all = preserve-fp→FPFunctor (preserve-all _) (preserve-all _)

module _ (𝒞P : HasProducts 𝒞) (𝒟P : HasProducts 𝒟) where

  private
    module 𝒞P = HasProducts 𝒞P
    module 𝒟P = HasProducts 𝒟P

  preserve-chosen-products : Set (o₁ ⊔ m₂ ⊔ e₂)
  preserve-chosen-products = ∀ {x y} → 𝒟.IsIso (𝒟P.pair (F.fmor (𝒞P.p₁ {x} {y})) (F.fmor (𝒞P.p₂ {x} {y})))

  module preserve-chosen-products-consequences (Fp : preserve-chosen-products) where

    mul : ∀ {x y} → 𝒟P.prod (F.fobj x) (F.fobj y) 𝒟.⇒ F.fobj (𝒞P.prod x y)
    mul = Fp .𝒟.IsIso.inverse

    mul⁻¹ : ∀ {x y} → F.fobj (𝒞P.prod x y) 𝒟.⇒ 𝒟P.prod (F.fobj x) (F.fobj y)
    mul⁻¹ {x} {y} = 𝒟P.pair (F.fmor (𝒞P.p₁ {x} {y})) (F.fmor (𝒞P.p₂ {x} {y}))

    mul-inv : ∀ {x y} → (mul {x} {y} 𝒟.∘ mul⁻¹) 𝒟.≈ 𝒟.id _
    mul-inv = Category.IsIso.inverse∘f≈id Fp

    mul⁻¹-natural : ∀ {x x' y y'} {f : x 𝒞.⇒ x'} {g : y 𝒞.⇒ y'} →
                  (mul⁻¹ 𝒟.∘ F.fmor (𝒞P.prod-m f g)) 𝒟.≈ (𝒟P.prod-m (F.fmor f) (F.fmor g) 𝒟.∘ mul⁻¹)
    mul⁻¹-natural {x} {x'} {y} {y'} {f} {g} = begin
        mul⁻¹ 𝒟.∘ F.fmor (𝒞P.prod-m f g)
      ≡⟨⟩
        𝒟P.pair (F.fmor 𝒞P.p₁) (F.fmor 𝒞P.p₂) 𝒟.∘ F.fmor (𝒞P.prod-m f g)
      ≈⟨ 𝒟P.pair-natural _ _ _ ⟩
        𝒟P.pair (F.fmor 𝒞P.p₁ 𝒟.∘ F.fmor (𝒞P.prod-m f g)) (F.fmor 𝒞P.p₂ 𝒟.∘ F.fmor (𝒞P.prod-m f g))
      ≈˘⟨ 𝒟P.pair-cong (F.fmor-comp _ _) (F.fmor-comp _ _) ⟩
        𝒟P.pair (F.fmor (𝒞P.p₁ 𝒞.∘ 𝒞P.prod-m f g)) (F.fmor (𝒞P.p₂ 𝒞.∘ 𝒞P.prod-m f g))
      ≈⟨ 𝒟P.pair-cong (F.fmor-cong (𝒞P.pair-p₁ _ _)) (F.fmor-cong (𝒞P.pair-p₂ _ _)) ⟩
        𝒟P.pair (F.fmor (f 𝒞.∘ 𝒞P.p₁)) (F.fmor (g 𝒞.∘ 𝒞P.p₂))
      ≈⟨ 𝒟P.pair-cong (F.fmor-comp _ _) (F.fmor-comp _ _) ⟩
        𝒟P.pair (F.fmor f 𝒟.∘ F.fmor 𝒞P.p₁) (F.fmor g 𝒟.∘ F.fmor 𝒞P.p₂)
      ≈˘⟨ 𝒟P.pair-compose _ _ _ _ ⟩
        𝒟P.prod-m (F.fmor f) (F.fmor g) 𝒟.∘ 𝒟P.pair (F.fmor 𝒞P.p₁) (F.fmor 𝒞P.p₂)
      ≡⟨⟩
        𝒟P.prod-m (F.fmor f) (F.fmor g) 𝒟.∘ mul⁻¹
      ∎
      where open ≈-Reasoning 𝒟.isEquiv

    mul-natural : ∀ {x x' y y'} {f : x 𝒞.⇒ x'} {g : y 𝒞.⇒ y'} →
                  (F.fmor (𝒞P.prod-m f g) 𝒟.∘ mul) 𝒟.≈ (mul 𝒟.∘ 𝒟P.prod-m (F.fmor f) (F.fmor g))
    mul-natural {x} {x'} {y} {y'} {f} {g} = begin
        F.fmor (𝒞P.prod-m f g) 𝒟.∘ mul
      ≈˘⟨ 𝒟.id-left ⟩
        𝒟.id _ 𝒟.∘ (F.fmor (𝒞P.prod-m f g) 𝒟.∘ mul)
      ≈˘⟨ 𝒟.∘-cong (Fp .𝒟.IsIso.inverse∘f≈id) 𝒟.≈-refl ⟩
        (mul 𝒟.∘ mul⁻¹) 𝒟.∘ (F.fmor (𝒞P.prod-m f g) 𝒟.∘ mul)
      ≈⟨ 𝒟.assoc _ _ _ ⟩
        mul 𝒟.∘ (mul⁻¹ 𝒟.∘ (F.fmor (𝒞P.prod-m f g) 𝒟.∘ mul))
      ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _) ⟩
        mul 𝒟.∘ ((mul⁻¹ 𝒟.∘ F.fmor (𝒞P.prod-m f g)) 𝒟.∘ mul)
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong mul⁻¹-natural 𝒟.≈-refl) ⟩
        mul 𝒟.∘ ((𝒟P.prod-m (F.fmor f) (F.fmor g) 𝒟.∘ mul⁻¹) 𝒟.∘ mul)
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _) ⟩
        mul 𝒟.∘ (𝒟P.prod-m (F.fmor f) (F.fmor g) 𝒟.∘ (mul⁻¹ 𝒟.∘ mul))
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong 𝒟.≈-refl (Fp .𝒟.IsIso.f∘inverse≈id)) ⟩
        mul 𝒟.∘ (𝒟P.prod-m (F.fmor f) (F.fmor g) 𝒟.∘ 𝒟.id _)
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right ⟩
        mul 𝒟.∘ 𝒟P.prod-m (F.fmor f) (F.fmor g)
      ∎
      where open ≈-Reasoning 𝒟.isEquiv

    F-p₁ : ∀ {x y} → (F.fmor (𝒞P.p₁ {x} {y}) 𝒟.∘ mul) 𝒟.≈ 𝒟P.p₁
    F-p₁ {x} {y} = begin
        F.fmor (𝒞P.p₁ {x} {y}) 𝒟.∘ mul
      ≈˘⟨ 𝒟.∘-cong (𝒟P.pair-p₁ _ _) 𝒟.≈-refl ⟩
        (𝒟P.p₁ 𝒟.∘ mul⁻¹) 𝒟.∘ mul
      ≈⟨ 𝒟.assoc _ _ _ ⟩
        𝒟P.p₁ 𝒟.∘ (mul⁻¹ 𝒟.∘ mul)
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (Fp .𝒟.IsIso.f∘inverse≈id) ⟩
        𝒟P.p₁ 𝒟.∘ 𝒟.id _
      ≈⟨ 𝒟.id-right ⟩
        𝒟P.p₁
      ∎
      where open ≈-Reasoning 𝒟.isEquiv

    F-p₁' : ∀ {x y} → F.fmor (𝒞P.p₁ {x} {y}) 𝒟.≈ (𝒟P.p₁ 𝒟.∘ mul⁻¹)
    F-p₁' {x} {y} = 𝒟.≈-sym (𝒟P.pair-p₁ _ _)

    F-p₂ : ∀ {x y} → (F.fmor (𝒞P.p₂ {x} {y}) 𝒟.∘ mul) 𝒟.≈ 𝒟P.p₂
    F-p₂ {x} {y} = begin
        F.fmor (𝒞P.p₂ {x} {y}) 𝒟.∘ mul
      ≈˘⟨ 𝒟.∘-cong (𝒟P.pair-p₂ _ _) 𝒟.≈-refl ⟩
        (𝒟P.p₂ 𝒟.∘ mul⁻¹) 𝒟.∘ mul
      ≈⟨ 𝒟.assoc _ _ _ ⟩
        𝒟P.p₂ 𝒟.∘ (mul⁻¹ 𝒟.∘ mul)
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (Fp .𝒟.IsIso.f∘inverse≈id) ⟩
        𝒟P.p₂ 𝒟.∘ 𝒟.id _
      ≈⟨ 𝒟.id-right ⟩
        𝒟P.p₂
      ∎
      where open ≈-Reasoning 𝒟.isEquiv

    F-pair : ∀ {x y z} {f₁ : x 𝒞.⇒ y} {f₂ : x 𝒞.⇒ z} →
            (mul 𝒟.∘ 𝒟P.pair (F.fmor f₁) (F.fmor f₂)) 𝒟.≈ F.fmor (𝒞P.pair f₁ f₂)
    F-pair {x} {y} {z} {f₁} {f₂} = begin
        mul 𝒟.∘ 𝒟P.pair (F.fmor f₁) (F.fmor f₂)
      ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟P.pair-cong (F.fmor-cong (𝒞P.pair-p₁ _ _)) (F.fmor-cong (𝒞P.pair-p₂ _ _))) ⟩
        mul 𝒟.∘ (𝒟P.pair (F.fmor (𝒞P.p₁ 𝒞.∘ 𝒞P.pair f₁ f₂)) (F.fmor (𝒞P.p₂ 𝒞.∘ 𝒞P.pair f₁ f₂)))
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟P.pair-cong (F.fmor-comp _ _) (F.fmor-comp _ _)) ⟩
        mul 𝒟.∘ (𝒟P.pair (F.fmor 𝒞P.p₁ 𝒟.∘ F.fmor (𝒞P.pair f₁ f₂)) (F.fmor 𝒞P.p₂ 𝒟.∘ F.fmor (𝒞P.pair f₁ f₂)))
      ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟P.pair-natural _ _ _) ⟩
        mul 𝒟.∘ (𝒟P.pair (F.fmor 𝒞P.p₁) (F.fmor 𝒞P.p₂) 𝒟.∘ F.fmor (𝒞P.pair f₁ f₂))
      ≡⟨⟩
        mul 𝒟.∘ (mul⁻¹ 𝒟.∘ F.fmor (𝒞P.pair f₁ f₂))
      ≈˘⟨ 𝒟.assoc _ _ _ ⟩
        (mul 𝒟.∘ mul⁻¹) 𝒟.∘ F.fmor (𝒞P.pair f₁ f₂)
      ≈⟨ 𝒟.∘-cong (Fp .𝒟.IsIso.inverse∘f≈id) 𝒟.≈-refl ⟩
        𝒟.id _ 𝒟.∘ F.fmor (𝒞P.pair f₁ f₂)
      ≈⟨ 𝒟.id-left ⟩
        F.fmor (𝒞P.pair f₁ f₂)
      ∎
      where open ≈-Reasoning 𝒟.isEquiv
