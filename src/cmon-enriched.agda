{-# OPTIONS --prop --postfix-projections --safe #-}

module cmon-enriched where

open import Level
open import categories
open import prop-setoid using (module ≈-Reasoning; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)

record CMonEnriched {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
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

record Biproduct {o m e} {𝒞 : Category o m e} (CM : CMonEnriched 𝒞) (A B : Category.obj 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open CMonEnriched CM
  open CommutativeMonoid
  field
    prod : obj
    p₁ : prod ⇒ A
    p₂ : prod ⇒ B
    in₁ : A ⇒ prod
    in₂ : B ⇒ prod

    id-1 : (p₁ ∘ in₁) ≈ id A
    id-2 : (p₂ ∘ in₂) ≈ id B
    zero-1 : (p₁ ∘ in₂) ≈ εm
    zero-2 : (p₂ ∘ in₁) ≈ εm
    id-+   : ((in₁ ∘ p₁) +m (in₂ ∘ p₂)) ≈ id prod

  -- This gives products
  pair : ∀ {x} → x ⇒ A → x ⇒ B → x ⇒ prod
  pair f g = (in₁ ∘ f) +m (in₂ ∘ g)

  pair-p₁ : ∀ {x} (f : x ⇒ A) (g : x ⇒ B) → (p₁ ∘ pair f g) ≈ f
  pair-p₁ f g =
    begin
      p₁ ∘ pair f g                       ≡⟨⟩
      p₁ ∘ ((in₁ ∘ f) +m (in₂ ∘ g))        ≈⟨ comp-bilinear₂ _ _ _ ⟩
      (p₁ ∘ (in₁ ∘ f)) +m (p₁ ∘ (in₂ ∘ g))  ≈˘⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
      ((p₁ ∘ in₁) ∘ f) +m ((p₁ ∘ in₂) ∘ g)  ≈⟨ homCM _ _ .+-cong (∘-cong id-1 ≈-refl) (∘-cong zero-1 ≈-refl) ⟩
      (id _ ∘ f) +m (εm ∘ g)               ≈⟨ homCM _ _ .+-cong id-left (comp-bilinear-ε₁ _) ⟩
      f +m εm                             ≈⟨ homCM _ _ .+-comm ⟩
      εm +m f                             ≈⟨ homCM _ _ .+-lunit ⟩
      f                                   ∎
    where open ≈-Reasoning isEquiv

  pair-p₂ : ∀ {x} (f : x ⇒ A) (g : x ⇒ B) → (p₂ ∘ pair f g) ≈ g
  pair-p₂ f g =
    begin
      p₂ ∘ pair f g                       ≡⟨⟩
      p₂ ∘ ((in₁ ∘ f) +m (in₂ ∘ g))        ≈⟨ comp-bilinear₂ _ _ _ ⟩
      (p₂ ∘ (in₁ ∘ f)) +m (p₂ ∘ (in₂ ∘ g))  ≈˘⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
      ((p₂ ∘ in₁) ∘ f) +m ((p₂ ∘ in₂) ∘ g)  ≈⟨ homCM _ _ .+-cong (∘-cong zero-2 ≈-refl) (∘-cong id-2 ≈-refl) ⟩
      (εm ∘ f) +m (id _ ∘ g)               ≈⟨ homCM _ _ .+-cong (comp-bilinear-ε₁ _) id-left ⟩
      εm +m g                             ≈⟨ homCM _ _ .+-lunit ⟩
      g                                   ∎
    where open ≈-Reasoning isEquiv

  pair-ext : ∀ {x} (f : x ⇒ prod) → pair (p₁ ∘ f) (p₂ ∘ f) ≈ f
  pair-ext f =
    begin
      pair (p₁ ∘ f) (p₂ ∘ f)              ≡⟨⟩
      (in₁ ∘ (p₁ ∘ f)) +m (in₂ ∘ (p₂ ∘ f)) ≈˘⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
      ((in₁ ∘ p₁) ∘ f) +m ((in₂ ∘ p₂) ∘ f) ≈˘⟨ comp-bilinear₁ _ _ _ ⟩
      ((in₁ ∘ p₁) +m (in₂ ∘ p₂)) ∘ f       ≈⟨ ∘-cong id-+ ≈-refl ⟩
      id _ ∘ f                            ≈⟨ id-left ⟩
      f                                   ∎
    where open ≈-Reasoning isEquiv

  -- And coproducts
  copair : ∀ {x} → A ⇒ x → B ⇒ x → prod ⇒ x
  copair f g = (f ∘ p₁) +m (g ∘ p₂)

  copair-in₁ : ∀ {x} (f : A ⇒ x) (g : B ⇒ x) → (copair f g ∘ in₁) ≈ f
  copair-in₁ f g =
    begin copair f g ∘ in₁                     ≡⟨⟩
           ((f ∘ p₁) +m (g ∘ p₂)) ∘ in₁         ≈⟨ comp-bilinear₁ _ _ _ ⟩
           ((f ∘ p₁) ∘ in₁) +m ((g ∘ p₂) ∘ in₁)  ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
           (f ∘ (p₁ ∘ in₁)) +m (g ∘ (p₂ ∘ in₁))  ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl id-1) (∘-cong ≈-refl zero-2) ⟩
           (f ∘ id _) +m (g ∘ εm)               ≈⟨ homCM _ _ .+-cong id-right (comp-bilinear-ε₂ _) ⟩
           f +m εm                             ≈⟨ homCM _ _ .+-comm ⟩
           εm +m f                             ≈⟨ homCM _ _ .+-lunit ⟩
           f                                  ∎
    where open ≈-Reasoning isEquiv

  copair-in₂ : ∀ {x} (f : A ⇒ x) (g : B ⇒ x) → (copair f g ∘ in₂) ≈ g
  copair-in₂ f g =
    begin copair f g ∘ in₂                     ≡⟨⟩
           ((f ∘ p₁) +m (g ∘ p₂)) ∘ in₂         ≈⟨ comp-bilinear₁ _ _ _ ⟩
           ((f ∘ p₁) ∘ in₂) +m ((g ∘ p₂) ∘ in₂)  ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
           (f ∘ (p₁ ∘ in₂)) +m (g ∘ (p₂ ∘ in₂))  ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl zero-1) (∘-cong ≈-refl id-2) ⟩
           (f ∘ εm) +m (g ∘ id _)               ≈⟨ homCM _ _ .+-cong (comp-bilinear-ε₂ _) id-right ⟩
           εm +m g                             ≈⟨ homCM _ _ .+-lunit ⟩
           g                                  ∎
    where open ≈-Reasoning isEquiv

  copair-ext : ∀ {x} (f : prod ⇒ x) → copair (f ∘ in₁) (f ∘ in₂) ≈ f
  copair-ext f =
    begin copair (f ∘ in₁) (f ∘ in₂)           ≡⟨⟩
           ((f ∘ in₁) ∘ p₁) +m ((f ∘ in₂) ∘ p₂) ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
           (f ∘ (in₁ ∘ p₁)) +m (f ∘ (in₂ ∘ p₂)) ≈˘⟨ comp-bilinear₂ _ _ _ ⟩
           f ∘ ((in₁ ∘ p₁) +m (in₂ ∘ p₂))       ≈⟨ ∘-cong ≈-refl id-+ ⟩
           f ∘ id _                            ≈⟨ id-right ⟩
           f ∎
    where open ≈-Reasoning isEquiv

-- Construct biproducts from products on a cmon-category
module cmon+products→biproducts {o m e} (𝒞 : Category o m e) (CM𝒞 : CMonEnriched 𝒞) (P : HasProducts 𝒞) where

  open Category 𝒞
  open CMonEnriched CM𝒞
  open CommutativeMonoid
  open IsEquivalence

  open HasProducts P

  -- Use the universal property of products to show that the pairing
  -- operation preserves addition.
  pair-+ : ∀ {x y z} (f₁ f₂ : x ⇒ y) (g₁ g₂ : x ⇒ z) →
     (pair f₁ g₁ +m pair f₂ g₂) ≈ pair (f₁ +m f₂) (g₁ +m g₂)
  pair-+ f₁ f₂ g₁ g₂ =
    begin
      pair f₁ g₁ +m pair f₂ g₂
    ≈⟨ ≈-sym (pair-ext _) ⟩
      pair (p₁ ∘ (pair f₁ g₁ +m pair f₂ g₂)) (p₂ ∘ (pair f₁ g₁ +m pair f₂ g₂))
    ≈⟨ pair-cong (comp-bilinear₂ _ _ _) (comp-bilinear₂ _ _ _) ⟩
      pair ((p₁ ∘ pair f₁ g₁) +m (p₁ ∘ pair f₂ g₂)) ((p₂ ∘ pair f₁ g₁) +m (p₂ ∘ pair f₂ g₂))
    ≈⟨ pair-cong (homCM _ _ .+-cong (pair-p₁ _ _) (pair-p₁ _ _)) (homCM _ _ .+-cong (pair-p₂ _ _) (pair-p₂ _ _)) ⟩
      pair (f₁ +m f₂) (g₁ +m g₂)
    ∎ where open ≈-Reasoning isEquiv

  _⊕_ = prod

  in₁ : ∀ {x y} → x ⇒ (x ⊕ y)
  in₁ = pair (id _) εm

  in₂ : ∀ {x y} → y ⇒ (x ⊕ y)
  in₂ = pair εm (id _)

  biproducts : ∀ x y → Biproduct CM𝒞 x y
  biproducts x y .Biproduct.prod = prod x y
  biproducts x y .Biproduct.p₁ = p₁
  biproducts x y .Biproduct.p₂ = p₂
  biproducts x y .Biproduct.in₁ = in₁
  biproducts x y .Biproduct.in₂ = in₂
  biproducts x y .Biproduct.id-1 = pair-p₁ _ _
  biproducts x y .Biproduct.id-2 = pair-p₂ _ _
  biproducts x y .Biproduct.zero-1 = pair-p₁ _ _
  biproducts x y .Biproduct.zero-2 = pair-p₂ _ _
  biproducts x y .Biproduct.id-+ =
    begin
      (in₁ ∘ p₁) +m (in₂ ∘ p₂) ≡⟨⟩
      (pair (id _) εm ∘ p₁) +m (pair εm (id _) ∘ p₂) ≈⟨ homCM _ _ .+-cong (pair-natural _ _ _) (pair-natural _ _ _) ⟩
      pair (id _ ∘ p₁) (εm ∘ p₁) +m pair (εm ∘ p₂) (id _ ∘ p₂) ≈⟨ homCM _ _ .+-cong (pair-cong id-left (comp-bilinear-ε₁ _)) (pair-cong (comp-bilinear-ε₁ _) id-left) ⟩
      pair p₁ εm +m pair εm p₂ ≈⟨ pair-+ _ _ _ _ ⟩
      pair (p₁ +m εm) (εm +m p₂) ≈⟨ pair-cong (isEquiv .trans (homCM _ _ .+-comm) (homCM _ _ .+-lunit)) (homCM _ _ .+-lunit) ⟩
      pair p₁ p₂ ≈⟨ pair-ext0 ⟩
      id _
    ∎
    where open ≈-Reasoning isEquiv

  -- additional biproduct bits
  --   https://arxiv.org/pdf/1801.06488



------------------------------------------------------------------------------
-- Additivity is inherited by functor categories
module _ {o₁ m₁ e₁ o₂ m₂ e₂}
         (𝒞 : Category o₁ m₁ e₁)
         (𝒟 : Category o₂ m₂ e₂)
         (CM : CMonEnriched 𝒟)
  where

  open import functor
  open CommutativeMonoid
  open CMonEnriched
  open NatTrans
  open ≃-NatTrans
  open Functor
  open IsEquivalence

  private
    module 𝒟 = Category 𝒟
    module CM = CMonEnriched CM

  homCM-F : ∀ F G → CommutativeMonoid (Category.hom-setoid [ 𝒞 ⇒ 𝒟 ] F G)
  homCM-F F G .ε .transf x = CM.εm
  homCM-F F G .ε .natural f =
    𝒟.isEquiv .trans (CM.comp-bilinear-ε₂ _) (𝒟.≈-sym (CM.comp-bilinear-ε₁ _))
  homCM-F F G ._+_ f₁ f₂ .transf x = CM.homCM _ _ ._+_ (f₁ .transf x) (f₂ .transf x)
  homCM-F F G ._+_ f₁ f₂ .natural {x} {y} f =
    begin
      G .fmor f 𝒟.∘ (f₁ .transf x CM.+m f₂ .transf x)
    ≈⟨ CM.comp-bilinear₂ _ _ _ ⟩
      (G .fmor f 𝒟.∘ f₁ .transf x) CM.+m (G .fmor f 𝒟.∘ f₂ .transf x)
    ≈⟨ CM.homCM _ _ .+-cong (f₁ .natural f) (f₂ .natural f) ⟩
      (f₁ .transf y 𝒟.∘ F .fmor f) CM.+m (f₂ .transf y 𝒟.∘ F .fmor f )
    ≈⟨ 𝒟.≈-sym (CM.comp-bilinear₁ _ _ _) ⟩
      (f₁ .transf y CM.+m f₂ .transf y) 𝒟.∘ F .fmor f
    ∎
    where open ≈-Reasoning 𝒟.isEquiv
  homCM-F F G .+-cong f₁≈f₂ g₁≈g₂ .transf-eq x = CM.homCM _ _ .+-cong (f₁≈f₂ .transf-eq x) (g₁≈g₂ .transf-eq x)
  homCM-F F G .+-lunit .transf-eq x = CM.homCM _ _ .+-lunit
  homCM-F F G .+-assoc .transf-eq x = CM.homCM _ _ .+-assoc
  homCM-F F G .+-comm .transf-eq x = CM.homCM _ _ .+-comm

  FunctorCat-cmon : CMonEnriched [ 𝒞 ⇒ 𝒟 ]
  FunctorCat-cmon .homCM = homCM-F
  FunctorCat-cmon .comp-bilinear₁ f₁ f₂ g .transf-eq x = CM.comp-bilinear₁ _ _ _
  FunctorCat-cmon .comp-bilinear₂ f g₁ g₂ .transf-eq x = CM.comp-bilinear₂ _ _ _
  FunctorCat-cmon .comp-bilinear-ε₁ f .transf-eq x = CM.comp-bilinear-ε₁ _
  FunctorCat-cmon .comp-bilinear-ε₂ f .transf-eq x = CM.comp-bilinear-ε₂ _
