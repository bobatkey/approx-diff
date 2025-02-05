{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level
open import prop
open import prop-setoid
  using (Setoid; IsEquivalence; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
open import categories
open import functor
open import setoid-cat

-- extra 'os' level is to raise the level of the codomain if needed
module yoneda {o m e} os es (𝒞 : Category o m e) where

PSh : Category (o ⊔ suc m ⊔ suc e ⊔ suc os ⊔ suc es) (o ⊔ suc m ⊔ suc os ⊔ suc e ⊔ suc es) (o ⊔ m ⊔ os ⊔ e ⊔ es)
PSh = [ opposite 𝒞 ⇒ SetoidCat (m ⊔ os) (e ⊔ es) ]

private
  module 𝒞 = Category 𝒞
open Setoid
open _⇒s_
open _≈s_
open IsEquivalence
open Functor
open NatTrans
open ≃-NatTrans

よ₀ : 𝒞.obj → PSh .Category.obj
よ₀ x .fobj y = Category.hom-setoid-l 𝒞 os es y x
よ₀ x .fmor f .func (lift g) = lift (g 𝒞.∘ f)
よ₀ x .fmor f .func-resp-≈ (lift g₁≈g₂) = lift (𝒞.∘-cong g₁≈g₂ 𝒞.≈-refl)
よ₀ x .fmor-cong {y} {z} {f₁} {f₂} f₁≈f₂ .func-eq {lift g₁} {lift g₂} (lift g₁≈g₂) = lift (𝒞.∘-cong g₁≈g₂ f₁≈f₂)
よ₀ x .fmor-id {y} .func-eq {lift g₁} {lift g₂} (lift g₁≈g₂) = lift (𝒞.isEquiv .trans 𝒞.id-right g₁≈g₂)
よ₀ x .fmor-comp {y} {z} {w} f g .func-eq {lift h₁} {lift h₂} (lift h₁≈h₂) .lower =
  begin
    h₁ 𝒞.∘ (g 𝒞.∘ f)    ≈⟨ 𝒞.∘-cong h₁≈h₂ 𝒞.≈-refl ⟩
    h₂ 𝒞.∘ (g 𝒞.∘ f)    ≈˘⟨ 𝒞.assoc _ _ _ ⟩
    ((h₂ 𝒞.∘ g) 𝒞.∘ f)  ∎
  where open ≈-Reasoning 𝒞.isEquiv

よ : Functor 𝒞 PSh
よ .fobj = よ₀
よ .fmor f .transf y .func (lift g) = lift (f 𝒞.∘ g)
よ .fmor f .transf y .func-resp-≈ (lift g₁≈g₂) = lift (𝒞.∘-cong 𝒞.≈-refl g₁≈g₂)
よ .fmor f .natural g .func-eq {lift h₁} {lift h₂} (lift h₁≈h₂) .lower =
  begin ((f 𝒞.∘ h₁) 𝒞.∘ g)   ≈⟨ 𝒞.∘-cong (𝒞.∘-cong 𝒞.≈-refl h₁≈h₂) 𝒞.≈-refl ⟩
         ((f 𝒞.∘ h₂) 𝒞.∘ g)  ≈⟨ 𝒞.assoc _ _ _ ⟩
         (f 𝒞.∘ (h₂ 𝒞.∘ g))  ∎
  where open ≈-Reasoning 𝒞.isEquiv
よ .fmor-cong {x} {y} {f₁} {f₂} f₁≈f₂ .transf-eq z .func-eq {lift g₁} {lift g₂} (lift g₁≈g₂) = lift (𝒞.∘-cong f₁≈f₂ g₁≈g₂)
よ .fmor-id .transf-eq x .func-eq {lift g₁} {lift g₂} (lift g₁≈g₂) .lower = 𝒞.isEquiv .trans 𝒞.id-left g₁≈g₂
よ .fmor-comp f g .transf-eq x .func-eq {lift h₁} {lift h₂} (lift h₁≈h₂) .lower =
  𝒞.isEquiv .trans (𝒞.∘-cong 𝒞.≈-refl h₁≈h₂) (𝒞.assoc _ _ _)

lemma₁ : ∀ F x → F .fobj x ⇒s Category.hom-setoid PSh (よ₀ x) F
lemma₁ F x .func Fx .transf y .func (lift f) = F .fmor f .func Fx
lemma₁ F x .func Fx .transf y .func-resp-≈ {lift f₁} {lift f₂} (lift f₁≈f₂) = F .fmor-cong f₁≈f₂ .func-eq (F .fobj x .refl)
lemma₁ F x .func Fx .natural {y} {z} g .func-eq {lift h₁} {lift h₂} (lift h₁≈h₂) =
  begin
    F .fmor g .func (F .fmor h₁ .func Fx)
  ≈⟨ F .fmor g .func-resp-≈ (F .fmor-cong h₁≈h₂ .func-eq (F .fobj x .refl)) ⟩
    F .fmor g .func (F .fmor h₂ .func Fx)
  ≈˘⟨ F .fmor-comp _ _ .func-eq (F .fobj x .refl) ⟩
    F .fmor (h₂ 𝒞.∘ g) .func Fx
  ∎ where open ≈-Reasoning (F .fobj z .isEquivalence)
lemma₁ F x .func-resp-≈ {Fx₁} {Fx₂} Fx₁≈Fx₂ .transf-eq y .func-eq {lift f₁} {lift f₂} (lift f₁≈f₂) = F .fmor-cong f₁≈f₂ .func-eq Fx₁≈Fx₂

lemma₂ : ∀ F x → Category.hom-setoid PSh (よ₀ x) F ⇒s F .fobj x
lemma₂ F x .func α = α .transf x .func (lift (𝒞.id _))
lemma₂ F x .func-resp-≈ {α₁}{α₂} α₁≈α₂ = α₁≈α₂ .transf-eq x .func-eq (lift 𝒞.≈-refl)

-- FIXME: lemma₁ ∘ lemma₂ = id and lemma₂ ∘ lemma₁ = id and both are natural.

open IsProduct

-- よ preserves products. FIXME: extend this to all limits
preserve-products : ∀ (x y p : 𝒞.obj) (p₁ : p 𝒞.⇒ x) (p₂ : p 𝒞.⇒ y) →
                    IsProduct {𝒞 = 𝒞} x y p p₁ p₂ →
                    IsProduct {𝒞 = PSh} (よ₀ x) (よ₀ y) (よ₀ p) (よ .fmor p₁) (よ .fmor p₂)
preserve-products x y p p₁ p₂ p-isproduct .pair {Z} f g .transf z .func Zz .lower =
  p-isproduct .pair (f .transf z .func Zz .lower) (g .transf z .func Zz .lower)
preserve-products x y p p₁ p₂ p-isproduct .pair {Z} f g .transf z .func-resp-≈ {Zz₁} {Zz₂} Zz₁≈Zz₂ .lower =
  p-isproduct .pair-cong (f .transf z .func-resp-≈ Zz₁≈Zz₂ .lower) (g .transf z .func-resp-≈ Zz₁≈Zz₂ .lower)
preserve-products x y p p₁ p₂ p-isproduct .pair {Z} f g .natural {x₁} {y₁} h .func-eq {Zz₁} {Zz₂} e .lower =
  begin
    p-isproduct .pair (f .transf x₁ .func Zz₁ .lower) (g .transf x₁ .func Zz₁ .lower) 𝒞.∘ h
  ≈⟨ pair-natural p-isproduct _ _ _ ⟩
    p-isproduct .pair (f .transf x₁ .func Zz₁ .lower 𝒞.∘ h) (g .transf x₁ .func Zz₁ .lower 𝒞.∘ h)
  ≈⟨ p-isproduct .pair-cong (f .natural h .func-eq e .lower) (g .natural h .func-eq e .lower) ⟩
    p-isproduct .pair (f .transf y₁ .func (Z .fmor h .func Zz₂) .lower) (g .transf y₁ .func (Z .fmor h .func Zz₂) .lower)
  ∎ where open ≈-Reasoning 𝒞.isEquiv
preserve-products x y p p₁ p₂ p-isproduct .pair-cong {Z} f₁≈f₂ g₁≈g₂ .transf-eq w .func-eq e .lower =
  p-isproduct .pair-cong (f₁≈f₂ .transf-eq w .func-eq e .lower) (g₁≈g₂ .transf-eq w .func-eq e .lower)
preserve-products x y p p₁ p₂ p-isproduct .pair-p₁ {Z} f g .transf-eq w .func-eq {Zw₁} {Zw₂} e .lower =
  begin
    p₁ 𝒞.∘ p-isproduct .pair (f .transf w .func Zw₁ .lower) (g .transf w .func Zw₁ .lower)
  ≈⟨ p-isproduct .pair-p₁ _ _ ⟩
    f .transf w .func Zw₁ .lower
  ≈⟨ f .transf w .func-resp-≈ e .lower ⟩
    f .transf w .func Zw₂ .lower
  ∎ where open ≈-Reasoning 𝒞.isEquiv
preserve-products x y p p₁ p₂ p-isproduct .pair-p₂ {Z} f g .transf-eq w .func-eq {Zw₁} {Zw₂} e .lower =
  begin
    p₂ 𝒞.∘ p-isproduct .pair (f .transf w .func Zw₁ .lower) (g .transf w .func Zw₁ .lower)
  ≈⟨ p-isproduct .pair-p₂ _ _ ⟩
    g .transf w .func Zw₁ .lower
  ≈⟨ g .transf w .func-resp-≈ e .lower ⟩
    g .transf w .func Zw₂ .lower
  ∎ where open ≈-Reasoning 𝒞.isEquiv
preserve-products x y p p₁ p₂ p-isproduct .pair-ext {Z} f .transf-eq w .func-eq {Zw₁} {Zw₂} e .lower =
  begin
    p-isproduct .pair (p₁ 𝒞.∘ f .transf w .func Zw₁ .lower) (p₂ 𝒞.∘ f .transf w .func Zw₁ .lower)
  ≈⟨ p-isproduct .pair-ext _ ⟩
    f .transf w .func Zw₁ .lower
  ≈⟨ f .transf w .func-resp-≈ e .lower ⟩
    f .transf w .func Zw₂ .lower
  ∎ where open ≈-Reasoning 𝒞.isEquiv
