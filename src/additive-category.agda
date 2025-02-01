{-# OPTIONS --prop --postfix-projections --safe #-}

module additive-category where

open import Level
open import categories
open import prop-setoid using (module ≈-Reasoning; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)

-- FIXME: without (bi)products, this is really PreAdditive
record AdditiveCat {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open CommutativeMonoid
  field
    homCM : ∀ x y → CommutativeMonoid (hom-setoid x y)

  _+m_ : ∀ {x y} → x ⇒ y → x ⇒ y → x ⇒ y
  f +m g = homCM _ _ ._+_ f g

  εm : ∀ {x y} → x ⇒ y
  εm {x} {y} = homCM x y .ε

  field
    comp-bilinear₁ : ∀ {X Y Z} (f₁ f₂ : Y ⇒ Z) (g : X ⇒ Y) →
                     ((f₁ +m f₂) ∘ g) ≈ ((f₁ ∘ g) +m (f₂ ∘ g))
    comp-bilinear₂ : ∀ {X Y Z} (f : Y ⇒ Z) (g₁ g₂ : X ⇒ Y) →
                     (f ∘ (g₁ +m g₂)) ≈ ((f ∘ g₁) +m (f ∘ g₂))
    comp-bilinear-ε₁ : ∀ {X Y Z} (f : X ⇒ Y) → (εm ∘ f) ≈ εm {X} {Z}
    comp-bilinear-ε₂ : ∀ {X Y Z} (f : Y ⇒ Z) → (f ∘ εm) ≈ εm {X} {Z}

-- Construct biproducts from products on an additive category
module _ {o m e} (𝒞 : Category o m e) (A𝒞 : AdditiveCat 𝒞) (P : HasProducts 𝒞) where

  open Category 𝒞
  open AdditiveCat A𝒞
  open CommutativeMonoid
  open IsEquivalence
  module P = HasProducts P

  -- Use the universal property of products to show that the pairing
  -- operation preserves addition.
  pair-+ : ∀ {x y z} (f₁ f₂ : x ⇒ y) (g₁ g₂ : x ⇒ z) →
     (P.pair f₁ g₁ +m P.pair f₂ g₂) ≈ P.pair (f₁ +m f₂) (g₁ +m g₂)
  pair-+ f₁ f₂ g₁ g₂ =
    begin
      P.pair f₁ g₁ +m P.pair f₂ g₂
    ≈⟨ ≈-sym (P.pair-ext _) ⟩
      P.pair (P.p₁ ∘ (P.pair f₁ g₁ +m P.pair f₂ g₂)) (P.p₂ ∘ (P.pair f₁ g₁ +m P.pair f₂ g₂))
    ≈⟨ P.pair-cong (comp-bilinear₂ _ _ _) (comp-bilinear₂ _ _ _) ⟩
      P.pair ((P.p₁ ∘ P.pair f₁ g₁) +m (P.p₁ ∘ P.pair f₂ g₂)) ((P.p₂ ∘ P.pair f₁ g₁) +m (P.p₂ ∘ P.pair f₂ g₂))
    ≈⟨ P.pair-cong (homCM _ _ .+-cong (P.pair-p₁ _ _) (P.pair-p₁ _ _)) (homCM _ _ .+-cong (P.pair-p₂ _ _) (P.pair-p₂ _ _)) ⟩
      P.pair (f₁ +m f₂) (g₁ +m g₂)
    ∎ where open ≈-Reasoning isEquiv

  _⊕_ = P.prod

  in₁ : ∀ {x y} → x ⇒ (x ⊕ y)
  in₁ = P.pair (id _) εm

  in₂ : ∀ {x y} → y ⇒ (x ⊕ y)
  in₂ = P.pair εm (id _)

  copair : ∀ {x y z} → x ⇒ z → y ⇒ z → (x ⊕ y) ⇒ z
  copair f g = (f ∘ P.p₁) +m (g ∘ P.p₂)

  copair-cong : ∀ {x y z} {f₁ f₂ : x ⇒ z} {g₁ g₂ : y ⇒ z} → f₁ ≈ f₂ → g₁ ≈ g₂ → copair f₁ g₁ ≈ copair f₂ g₂
  copair-cong f₁≈f₂ g₁≈g₂ = homCM _ _ .+-cong (∘-cong f₁≈f₂ ≈-refl) (∘-cong g₁≈g₂ ≈-refl)

  copair-in₁ : ∀ {x y z} (f : x ⇒ z) (g : y ⇒ z) → (copair f g ∘ in₁) ≈ f
  copair-in₁ f g =
    begin
      ((f ∘ P.p₁) +m (g ∘ P.p₂)) ∘ P.pair (id _) εm
    ≈⟨ comp-bilinear₁ _ _ _ ⟩
      ((f ∘ P.p₁) ∘ P.pair (id _) εm) +m ((g ∘ P.p₂) ∘ P.pair (id _) εm)
    ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
      (f ∘ (P.p₁ ∘ P.pair (id _) εm)) +m (g ∘ (P.p₂ ∘ P.pair (id _) εm))
    ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl (P.pair-p₁ _ _)) (∘-cong ≈-refl (P.pair-p₂ _ _)) ⟩
      (f ∘ id _) +m (g ∘ εm)
    ≈⟨ homCM _ _ .+-cong id-right (comp-bilinear-ε₂ g) ⟩
      f  +m εm
    ≈⟨ homCM _ _ .+-comm ⟩
      εm  +m f
    ≈⟨ homCM _ _ .+-lunit ⟩
      f
    ∎
    where open ≈-Reasoning isEquiv

  copair-in₂ : ∀ {x y z} (f : x ⇒ z) (g : y ⇒ z) → (copair f g ∘ in₂) ≈ g
  copair-in₂ f g =
    begin
      ((f ∘ P.p₁) +m (g ∘ P.p₂)) ∘ P.pair εm (id _)
    ≈⟨ comp-bilinear₁ _ _ _ ⟩
      ((f ∘ P.p₁) ∘ P.pair εm (id _)) +m ((g ∘ P.p₂) ∘ P.pair εm (id _))
    ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
      (f ∘ (P.p₁ ∘ P.pair εm (id _))) +m (g ∘ (P.p₂ ∘ P.pair εm (id _)))
    ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl (P.pair-p₁ _ _)) (∘-cong ≈-refl (P.pair-p₂ _ _)) ⟩
      (f ∘ εm) +m (g ∘ id _)
    ≈⟨ homCM _ _ .+-cong (comp-bilinear-ε₂ f) id-right ⟩
      εm  +m g
    ≈⟨ homCM _ _ .+-lunit ⟩
      g
    ∎
    where open ≈-Reasoning isEquiv

  copair-ext : ∀ {x y z} (f : (x ⊕ y) ⇒ z) → copair (f ∘ in₁) (f ∘ in₂) ≈ f
  copair-ext f =
    begin
      ((f ∘ P.pair (id _) εm) ∘ P.p₁) +m ((f ∘ P.pair εm (id _)) ∘ P.p₂)
    ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
      (f ∘ (P.pair (id _) εm ∘ P.p₁)) +m (f ∘ (P.pair εm (id _) ∘ P.p₂))
    ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl (P.pair-natural _ _ _)) (∘-cong ≈-refl (P.pair-natural _ _ _)) ⟩
      (f ∘ P.pair (id _ ∘ P.p₁) (εm ∘ P.p₁)) +m (f ∘ P.pair (εm ∘ P.p₂) (id _ ∘ P.p₂))
    ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl (P.pair-cong id-left (comp-bilinear-ε₁ _)))
                         (∘-cong ≈-refl (P.pair-cong (comp-bilinear-ε₁ _) id-left)) ⟩
      (f ∘ P.pair P.p₁ εm) +m (f ∘ P.pair εm P.p₂)
    ≈⟨ ≈-sym (comp-bilinear₂ _ _ _) ⟩
      f ∘ (P.pair P.p₁ εm +m P.pair εm P.p₂)
    ≈⟨ ∘-cong ≈-refl (pair-+ _ _ _ _) ⟩
      f ∘ P.pair (P.p₁ +m εm) (εm +m P.p₂)
    ≈⟨ ∘-cong ≈-refl (P.pair-cong (isEquiv .trans (homCM _ _ .+-comm) (homCM _ _ .+-lunit)) (homCM _ _ .+-lunit)) ⟩
      f ∘ P.pair P.p₁ P.p₂
    ≈⟨ ∘-cong ≈-refl P.pair-ext0 ⟩
      f ∘ id _
    ≈⟨ id-right ⟩
      f
    ∎ where open ≈-Reasoning isEquiv

  coproducts : HasCoproducts 𝒞
  coproducts .HasCoproducts.coprod = P.prod
  coproducts .HasCoproducts.in₁ = in₁
  coproducts .HasCoproducts.in₂ = in₂
  coproducts .HasCoproducts.copair = copair
  coproducts .HasCoproducts.copair-cong = copair-cong
  coproducts .HasCoproducts.copair-in₁ = copair-in₁
  coproducts .HasCoproducts.copair-in₂ = copair-in₂
  coproducts .HasCoproducts.copair-ext = copair-ext

-- Additivity is inherited by functor categories
module _ {o₁ m₁ e₁ o₂ m₂ e₂}
         (𝒞 : Category o₁ m₁ e₁)
         (𝒟 : Category o₂ m₂ e₂)
         (A  : AdditiveCat 𝒟)
  where

  open import functor
  open CommutativeMonoid
  open AdditiveCat
  open NatTrans
  open ≃-NatTrans
  open Functor
  open IsEquivalence

  private
    module 𝒟 = Category 𝒟
    module A = AdditiveCat A

  homCM-F : ∀ F G → CommutativeMonoid (Category.hom-setoid [ 𝒞 ⇒ 𝒟 ] F G)
  homCM-F F G .ε .transf x = A.εm
  homCM-F F G .ε .natural f =
    𝒟.isEquiv .trans (A.comp-bilinear-ε₂ _) (𝒟.≈-sym (A.comp-bilinear-ε₁ _))
  homCM-F F G ._+_ f₁ f₂ .transf x = A.homCM _ _ ._+_ (f₁ .transf x) (f₂ .transf x)
  homCM-F F G ._+_ f₁ f₂ .natural {x} {y} f =
    begin
      G .fmor f 𝒟.∘ (f₁ .transf x A.+m f₂ .transf x)
    ≈⟨ A.comp-bilinear₂ _ _ _ ⟩
      (G .fmor f 𝒟.∘ f₁ .transf x) A.+m (G .fmor f 𝒟.∘ f₂ .transf x)
    ≈⟨ A.homCM _ _ .+-cong (f₁ .natural f) (f₂ .natural f) ⟩
      (f₁ .transf y 𝒟.∘ F .fmor f) A.+m (f₂ .transf y 𝒟.∘ F .fmor f )
    ≈⟨ 𝒟.≈-sym (A.comp-bilinear₁ _ _ _) ⟩
      (f₁ .transf y A.+m f₂ .transf y) 𝒟.∘ F .fmor f
    ∎
    where open ≈-Reasoning 𝒟.isEquiv
  homCM-F F G .+-cong f₁≈f₂ g₁≈g₂ .transf-eq x = A.homCM _ _ .+-cong (f₁≈f₂ .transf-eq x) (g₁≈g₂ .transf-eq x)
  homCM-F F G .+-lunit .transf-eq x = A.homCM _ _ .+-lunit
  homCM-F F G .+-assoc .transf-eq x = A.homCM _ _ .+-assoc
  homCM-F F G .+-comm .transf-eq x = A.homCM _ _ .+-comm

  FunctorCat-additive : AdditiveCat [ 𝒞 ⇒ 𝒟 ]
  FunctorCat-additive .homCM = homCM-F
  FunctorCat-additive .comp-bilinear₁ f₁ f₂ g .transf-eq x = A.comp-bilinear₁ _ _ _
  FunctorCat-additive .comp-bilinear₂ f g₁ g₂ .transf-eq x = A.comp-bilinear₂ _ _ _
  FunctorCat-additive .comp-bilinear-ε₁ f .transf-eq x = A.comp-bilinear-ε₁ _
  FunctorCat-additive .comp-bilinear-ε₂ f .transf-eq x = A.comp-bilinear-ε₂ _
