{-# OPTIONS --prop --postfix-projections --safe #-}

module cmon-enriched where

open import Level
open import categories using (Category; HasProducts; HasCoproducts; Product)
open import product-category using (product)
open import prop-setoid using (module ≈-Reasoning; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)

-- Additional biproduct bits:
--   https://arxiv.org/pdf/1801.06488

record CMonEnriched {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open CommutativeMonoid
  open IsEquivalence
  field
    homCM : ∀ x y → CommutativeMonoid (hom-setoid x y)

  _+m_ : ∀ {x y} → x ⇒ y → x ⇒ y → x ⇒ y
  f +m g = homCM _ _ ._+_ f g

  εm : ∀ {x y} → x ⇒ y
  εm {x} {y} = homCM x y .ε

  +m-runit : ∀ {x y} {f : x ⇒ y} → (f +m εm) ≈ f
  +m-runit = isEquiv .trans (homCM _ _ .+-comm) (homCM _ _ .+-lunit)

  field
    comp-bilinear₁ : ∀ {X Y Z} (f₁ f₂ : Y ⇒ Z) (g : X ⇒ Y) →
                     ((f₁ +m f₂) ∘ g) ≈ ((f₁ ∘ g) +m (f₂ ∘ g))
    comp-bilinear₂ : ∀ {X Y Z} (f : Y ⇒ Z) (g₁ g₂ : X ⇒ Y) →
                     (f ∘ (g₁ +m g₂)) ≈ ((f ∘ g₁) +m (f ∘ g₂))
    comp-bilinear-ε₁ : ∀ {X Y Z} (f : X ⇒ Y) → (εm ∘ f) ≈ εm {X} {Z}
    comp-bilinear-ε₂ : ∀ {X Y Z} (f : Y ⇒ Z) → (f ∘ εm) ≈ εm {X} {Z}

module _ {o m e} {𝒞 : Category o m e} (CM : CMonEnriched 𝒞) where
  open Category 𝒞
  open CMonEnriched
  open CommutativeMonoid

  op-cmon-enriched : CMonEnriched (Category.opposite 𝒞)
  op-cmon-enriched .homCM x y .ε = CM .homCM y x .ε
  op-cmon-enriched .homCM x y ._+_ = CM .homCM y x ._+_
  op-cmon-enriched .homCM x y .+-cong = CM .homCM y x .+-cong
  op-cmon-enriched .homCM x y .+-lunit = CM .homCM y x .+-lunit
  op-cmon-enriched .homCM x y .+-assoc = CM .homCM y x .+-assoc
  op-cmon-enriched .homCM x y .+-comm = CM .homCM y x .+-comm
  op-cmon-enriched .comp-bilinear₁ f₁ f₂ g = CM .comp-bilinear₂ g f₁ f₂
  op-cmon-enriched .comp-bilinear₂ f g₁ g₂ = CM .comp-bilinear₁ g₁ g₂ f
  op-cmon-enriched .comp-bilinear-ε₁ = CM .comp-bilinear-ε₂
  op-cmon-enriched .comp-bilinear-ε₂ = CM .comp-bilinear-ε₁

module _ {o₁ m₁ e₁ o₂ m₂ e₃} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₃}
         (CM𝒞 : CMonEnriched 𝒞) (CM𝒟 : CMonEnriched 𝒟) where

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
  open CMonEnriched
  open CommutativeMonoid
  open import Data.Product using (_,_; proj₁; proj₂)
  open import prop using (_,_; proj₁; proj₂)

  product-cmon-enriched : CMonEnriched (product 𝒞 𝒟)
  product-cmon-enriched .homCM (x₁ , x₂) (y₁ , y₂) .ε = (ε (homCM CM𝒞 x₁ y₁)) , (ε (homCM CM𝒟 x₂ y₂))
  product-cmon-enriched .homCM (x₁ , x₂) (y₁ , y₂) ._+_ (f₁ , f₂) (g₁ , g₂) =
    CM𝒞 .homCM x₁ y₁ ._+_ f₁ g₁ , CM𝒟 .homCM x₂ y₂ ._+_ f₂ g₂
  product-cmon-enriched .homCM (x₁ , x₂) (y₁ , y₂) .+-cong (f₁≈f₁' , f₂≈f₂') (g₁≈g₁' , g₂≈g₂') =
    +-cong (homCM CM𝒞 x₁ y₁) f₁≈f₁' g₁≈g₁' ,
    +-cong (homCM CM𝒟 x₂ y₂) f₂≈f₂' g₂≈g₂'
  product-cmon-enriched .homCM (x₁ , x₂) (y₁ , y₂) .+-lunit = +-lunit (homCM CM𝒞 x₁ y₁) , +-lunit (homCM CM𝒟 x₂ y₂)
  product-cmon-enriched .homCM (x₁ , x₂) (y₁ , y₂) .+-assoc = +-assoc (homCM CM𝒞 x₁ y₁) , +-assoc (homCM CM𝒟 x₂ y₂)
  product-cmon-enriched .homCM (x₁ , x₂) (y₁ , y₂) .+-comm = +-comm (homCM CM𝒞 x₁ y₁) , +-comm (homCM CM𝒟 x₂ y₂)
  product-cmon-enriched .comp-bilinear₁ f₁ f₂ g =
    CM𝒞 .comp-bilinear₁ (f₁ .proj₁) (f₂ .proj₁) (g .proj₁) ,
    CM𝒟 .comp-bilinear₁ (f₁ .proj₂) (f₂ .proj₂) (g .proj₂)
  product-cmon-enriched .comp-bilinear₂ f g₁ g₂ =
    comp-bilinear₂ CM𝒞 (f .proj₁) (g₁ .proj₁) (g₂ .proj₁) ,
    comp-bilinear₂ CM𝒟 (f .proj₂) (g₁ .proj₂) (g₂ .proj₂)
  product-cmon-enriched .comp-bilinear-ε₁ f =
    comp-bilinear-ε₁ CM𝒞 (f .proj₁) , comp-bilinear-ε₁ CM𝒟 (f .proj₂)
  product-cmon-enriched .comp-bilinear-ε₂ f =
    comp-bilinear-ε₂ CM𝒞 (f .proj₁) , comp-bilinear-ε₂ CM𝒟 (f .proj₂)


module _ {o m e} {𝒞 : Category o m e} (CM : CMonEnriched 𝒞) where
  open Category 𝒞
  open CMonEnriched CM
  open CommutativeMonoid

  record Biproduct  (A B : Category.obj 𝒞) : Set (o ⊔ m ⊔ e) where
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

    pair-cong : ∀ {x} {f₁ f₂ : x ⇒ A} {g₁ g₂ : x ⇒ B} →
                f₁ ≈ f₂ → g₁ ≈ g₂ → pair f₁ g₁ ≈ pair f₂ g₂
    pair-cong f₁≈f₂ g₁≈g₂ = homCM _ _ .+-cong (∘-cong ≈-refl f₁≈f₂) (∘-cong ≈-refl g₁≈g₂)

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

    pair-ext0 : pair p₁ p₂ ≈ id prod
    pair-ext0 = ≈-trans (≈-sym (pair-cong id-right id-right)) (pair-ext (id _))

    -- And coproducts
    copair : ∀ {x} → A ⇒ x → B ⇒ x → prod ⇒ x
    copair f g = (f ∘ p₁) +m (g ∘ p₂)

    copair-cong : ∀ {x} {f₁ f₂ : A ⇒ x} {g₁ g₂ : B ⇒ x} →
                    f₁ ≈ f₂ → g₁ ≈ g₂ → copair f₁ g₁ ≈ copair f₂ g₂
    copair-cong f₁≈f₂ g₁≈g₂ = homCM _ _ .+-cong (∘-cong f₁≈f₂ ≈-refl) (∘-cong g₁≈g₂ ≈-refl)

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

  module _ where

    open Biproduct

    biproducts→products : (∀ x y → Biproduct x y) → HasProducts 𝒞
    biproducts→products bp .HasProducts.prod x y = prod (bp x y)
    biproducts→products bp .HasProducts.p₁ {x} {y} = p₁ (bp x y)
    biproducts→products bp .HasProducts.p₂ {x} {y} = p₂ (bp x y)
    biproducts→products bp .HasProducts.pair {x} {y} {z} = pair (bp y z)
    biproducts→products bp .HasProducts.pair-cong {x} {y} {z} = pair-cong (bp y z)
    biproducts→products bp .HasProducts.pair-p₁ {x} {y} {z} = pair-p₁ (bp y z)
    biproducts→products bp .HasProducts.pair-p₂ {x} {y} {z} = pair-p₂ (bp y z)
    biproducts→products bp .HasProducts.pair-ext {x} {y} {z} = pair-ext (bp y z)

    biproducts→coproducts : (∀ x y → Biproduct x y) → HasCoproducts 𝒞
    biproducts→coproducts bp .HasCoproducts.coprod x y = prod (bp x y)
    biproducts→coproducts bp .HasCoproducts.in₁ {x} {y} = in₁ (bp x y)
    biproducts→coproducts bp .HasCoproducts.in₂ {x} {y} = in₂ (bp x y)
    biproducts→coproducts bp .HasCoproducts.copair {x} {y} = copair (bp x y)
    biproducts→coproducts bp .HasCoproducts.copair-cong {x} {y} = copair-cong (bp x y)
    biproducts→coproducts bp .HasCoproducts.copair-in₁ {x} {y} = copair-in₁ (bp x y)
    biproducts→coproducts bp .HasCoproducts.copair-in₂ {x} {y} = copair-in₂ (bp x y)
    biproducts→coproducts bp .HasCoproducts.copair-ext {x} {y} = copair-ext (bp x y)

  module _ (BP : ∀ x y → Biproduct x y) where

    open HasProducts (biproducts→products BP)
    open HasCoproducts (biproducts→coproducts BP)

    in₁-natural : ∀ {x₁ y₁ x₂ y₂} {f : x₁ ⇒ y₁} {g : x₂ ⇒ y₂} →
                  (prod-m f g ∘ in₁) ≈ (in₁ ∘ f)
    in₁-natural {f = f} {g = g} =
      begin
        ((in₁ ∘ (f ∘ p₁)) +m (in₂ ∘ (g ∘ p₂))) ∘ in₁
      ≈⟨ comp-bilinear₁ _ _ _ ⟩
        ((in₁ ∘ (f ∘ p₁)) ∘ in₁) +m ((in₂ ∘ (g ∘ p₂)) ∘ in₁)
      ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
        (in₁ ∘ ((f ∘ p₁) ∘ in₁)) +m (in₂ ∘ ((g ∘ p₂) ∘ in₁))
      ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl (assoc _ _ _)) (∘-cong ≈-refl (assoc _ _ _)) ⟩
        (in₁ ∘ (f ∘ (p₁ ∘ in₁))) +m (in₂ ∘ (g ∘ (p₂ ∘ in₁)))
      ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl (∘-cong ≈-refl (BP _ _ .Biproduct.id-1))) (∘-cong ≈-refl (∘-cong ≈-refl (BP _ _ .Biproduct.zero-2))) ⟩
        (in₁ ∘ (f ∘ id _)) +m (in₂ ∘ (g ∘ εm))
      ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl id-right) (∘-cong ≈-refl (comp-bilinear-ε₂ _)) ⟩
        (in₁ ∘ f) +m (in₂ ∘ εm)
      ≈⟨ homCM _ _ .+-cong ≈-refl (comp-bilinear-ε₂ _) ⟩
        (in₁ ∘ f) +m εm
      ≈⟨ +m-runit ⟩
        in₁ ∘ f
      ∎ where open ≈-Reasoning isEquiv

    in₂-natural : ∀ {x₁ y₁ x₂ y₂} {f : x₁ ⇒ y₁} {g : x₂ ⇒ y₂} →
                  (prod-m f g ∘ in₂) ≈ (in₂ ∘ g)
    in₂-natural {f = f} {g = g} =
      begin
        ((in₁ ∘ (f ∘ p₁)) +m (in₂ ∘ (g ∘ p₂))) ∘ in₂
      ≈⟨ comp-bilinear₁ _ _ _ ⟩
        ((in₁ ∘ (f ∘ p₁)) ∘ in₂) +m ((in₂ ∘ (g ∘ p₂)) ∘ in₂)
      ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
        (in₁ ∘ ((f ∘ p₁) ∘ in₂)) +m (in₂ ∘ ((g ∘ p₂) ∘ in₂))
      ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl (assoc _ _ _)) (∘-cong ≈-refl (assoc _ _ _)) ⟩
        (in₁ ∘ (f ∘ (p₁ ∘ in₂))) +m (in₂ ∘ (g ∘ (p₂ ∘ in₂)))
      ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl (∘-cong ≈-refl (BP _ _ .Biproduct.zero-1))) (∘-cong ≈-refl (∘-cong ≈-refl (BP _ _ .Biproduct.id-2))) ⟩
        (in₁ ∘ (f ∘ εm)) +m (in₂ ∘ (g ∘ id _))
      ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl (comp-bilinear-ε₂ _)) (∘-cong ≈-refl id-right) ⟩
        (in₁ ∘ εm) +m (in₂ ∘ g)
      ≈⟨ homCM _ _ .+-cong (comp-bilinear-ε₂ _) ≈-refl ⟩
        εm +m (in₂ ∘ g)
      ≈⟨ homCM _ _ .+-lunit ⟩
        in₂ ∘ g
      ∎ where open ≈-Reasoning isEquiv

    copair-prod : ∀ {x₁ x₂ y₁ y₂ z}
                    {f₁ : x₂ ⇒ z} {g₁ : y₂ ⇒ z}
                    {f₂ : x₁ ⇒ x₂} {g₂ : y₁ ⇒ y₂} →
                  (copair f₁ g₁ ∘ prod-m f₂ g₂) ≈ copair (f₁ ∘ f₂) (g₁ ∘ g₂)
    copair-prod {f₁ = f₁} {g₁ = g₁} {f₂ = f₂} {g₂ = g₂} =
      begin
        copair f₁ g₁ ∘ prod-m f₂ g₂
      ≡⟨⟩
        ((f₁ ∘ p₁) +m (g₁ ∘ p₂)) ∘ ((in₁ ∘ (f₂ ∘ p₁)) +m (in₂ ∘ (g₂ ∘ p₂)))
      ≈⟨ comp-bilinear₁ _ _ _ ⟩
        ((f₁ ∘ p₁) ∘ ((in₁ ∘ (f₂ ∘ p₁)) +m (in₂ ∘ (g₂ ∘ p₂)))) +m ((g₁ ∘ p₂) ∘ ((in₁ ∘ (f₂ ∘ p₁)) +m (in₂ ∘ (g₂ ∘ p₂))))
      ≈⟨ homCM _ _ .+-cong (comp-bilinear₂ _ _ _) (comp-bilinear₂ _ _ _) ⟩
        (((f₁ ∘ p₁) ∘ (in₁ ∘ (f₂ ∘ p₁))) +m ((f₁ ∘ p₁) ∘ (in₂ ∘ (g₂ ∘ p₂)))) +m (((g₁ ∘ p₂) ∘ (in₁ ∘ (f₂ ∘ p₁))) +m ((g₁ ∘ p₂) ∘ (in₂ ∘ (g₂ ∘ p₂))))
      ≈⟨ homCM _ _ .+-cong (homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _)) (homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _)) ⟩
        ((f₁ ∘ (p₁ ∘ (in₁ ∘ (f₂ ∘ p₁)))) +m (f₁ ∘ (p₁ ∘ (in₂ ∘ (g₂ ∘ p₂))))) +m ((g₁ ∘ (p₂ ∘ (in₁ ∘ (f₂ ∘ p₁)))) +m (g₁ ∘ (p₂ ∘ (in₂ ∘ (g₂ ∘ p₂)))))
      ≈˘⟨ homCM _ _ .+-cong (homCM _ _ .+-cong (∘-cong ≈-refl (assoc _ _ _)) (∘-cong ≈-refl (assoc _ _ _))) (homCM _ _ .+-cong (∘-cong ≈-refl (assoc _ _ _)) (∘-cong ≈-refl (assoc _ _ _))) ⟩
        ((f₁ ∘ ((p₁ ∘ in₁) ∘ (f₂ ∘ p₁))) +m (f₁ ∘ ((p₁ ∘ in₂) ∘ (g₂ ∘ p₂)))) +m ((g₁ ∘ ((p₂ ∘ in₁) ∘ (f₂ ∘ p₁))) +m (g₁ ∘ ((p₂ ∘ in₂) ∘ (g₂ ∘ p₂))))
      ≈⟨ homCM _ _ .+-cong (homCM _ _ .+-cong (∘-cong ≈-refl (∘-cong (BP _ _ .Biproduct.id-1) ≈-refl))
                                              (∘-cong ≈-refl (∘-cong (BP _ _ .Biproduct.zero-1) ≈-refl)))
                           (homCM _ _ .+-cong (∘-cong ≈-refl (∘-cong (BP _ _ .Biproduct.zero-2) ≈-refl))
                                              (∘-cong ≈-refl (∘-cong (BP _ _ .Biproduct.id-2) ≈-refl))) ⟩
        ((f₁ ∘ (id _ ∘ (f₂ ∘ p₁))) +m (f₁ ∘ (εm ∘ (g₂ ∘ p₂)))) +m ((g₁ ∘ (εm ∘ (f₂ ∘ p₁))) +m (g₁ ∘ (id _ ∘ (g₂ ∘ p₂))))
      ≈⟨ homCM _ _ .+-cong (homCM _ _ .+-cong (∘-cong ≈-refl id-left) (∘-cong ≈-refl (comp-bilinear-ε₁ _)))
                           (homCM _ _ .+-cong (∘-cong ≈-refl (comp-bilinear-ε₁ _)) (∘-cong ≈-refl id-left)) ⟩
        ((f₁ ∘ (f₂ ∘ p₁)) +m (f₁ ∘ εm)) +m ((g₁ ∘ εm) +m (g₁ ∘ (g₂ ∘ p₂)))
      ≈⟨ homCM _ _ .+-cong (homCM _ _ .+-cong (≈-sym (assoc _ _ _)) (comp-bilinear-ε₂ _))
                           (homCM _ _ .+-cong (comp-bilinear-ε₂ _) (≈-sym (assoc _ _ _))) ⟩
        (((f₁ ∘ f₂) ∘ p₁) +m εm) +m (εm +m ((g₁ ∘ g₂) ∘ p₂))
      ≈⟨ homCM _ _ .+-cong +m-runit (homCM _ _ .+-lunit) ⟩
        ((f₁ ∘ f₂) ∘ p₁) +m ((g₁ ∘ g₂) ∘ p₂)
      ≡⟨⟩
        copair (f₁ ∘ f₂) (g₁ ∘ g₂)
      ∎ where open ≈-Reasoning isEquiv

------------------------------------------------------------------------------
-- Construct biproducts from coproducts on a cmon-category
module cmon+coproduct→biproduct {o m e}
         {𝒞 : Category o m e} (CM𝒞 : CMonEnriched 𝒞)
         (CP : HasCoproducts 𝒞) where

  open Category 𝒞
  open CMonEnriched CM𝒞
  open CommutativeMonoid
  open IsEquivalence

  open HasCoproducts CP

  copair-ε : ∀ {x y z} → copair εm εm ≈ εm {coprod x y} {z}
  copair-ε =
    begin
      copair εm εm                  ≈˘⟨ copair-cong (comp-bilinear-ε₁ in₁) (comp-bilinear-ε₁ in₂) ⟩
      copair (εm ∘ in₁ ) (εm ∘ in₂) ≈⟨ copair-ext εm ⟩
      εm                            ∎
    where open ≈-Reasoning isEquiv

  copair-+ : ∀ {x y z} (f₁ f₂ : x ⇒ z) (g₁ g₂ : y ⇒ z) →
    (copair f₁ g₁ +m copair f₂ g₂) ≈ copair (f₁ +m f₂) (g₁ +m g₂)
  copair-+ f₁ f₂ g₁ g₂ =
    begin
      copair f₁ g₁ +m copair f₂ g₂
    ≈˘⟨ copair-ext _ ⟩
      copair ((copair f₁ g₁ +m copair f₂ g₂) ∘ in₁) ((copair f₁ g₁ +m copair f₂ g₂) ∘ in₂)
    ≈⟨ copair-cong (comp-bilinear₁ _ _ _) (comp-bilinear₁ _ _ _) ⟩
      copair ((copair f₁ g₁ ∘ in₁) +m (copair f₂ g₂ ∘ in₁)) ((copair f₁ g₁ ∘ in₂) +m (copair f₂ g₂ ∘ in₂))
    ≈⟨ copair-cong (homCM _ _ .+-cong (copair-in₁ _ _) (copair-in₁ _ _)) (homCM _ _ .+-cong (copair-in₂ _ _) (copair-in₂ _ _)) ⟩
      copair (f₁ +m f₂) (g₁ +m g₂)
    ∎ where open ≈-Reasoning isEquiv

  biproduct : ∀ {x y} → Biproduct CM𝒞 x y
  biproduct {x} {y} .Biproduct.prod = coprod x y
  biproduct .Biproduct.p₁ = copair (id _) εm
  biproduct .Biproduct.p₂ = copair εm (id _)
  biproduct .Biproduct.in₁ = in₁
  biproduct .Biproduct.in₂ = in₂
  biproduct .Biproduct.id-1 = copair-in₁ _ _
  biproduct .Biproduct.id-2 = copair-in₂ _ _
  biproduct .Biproduct.zero-1 = copair-in₂ _ _
  biproduct .Biproduct.zero-2 = copair-in₁ _ _
  biproduct {x} {y} .Biproduct.id-+ =
    begin
      (in₁ ∘ copair (id x) εm) +m (in₂ ∘ copair εm (id y))
    ≈⟨ homCM _ _ .+-cong (copair-natural _ _ _) (copair-natural _ _ _) ⟩
      copair (in₁ ∘ id x) (in₁ ∘ εm) +m copair (in₂ ∘ εm) (in₂ ∘ id y)
    ≈⟨ homCM _ _ .+-cong (copair-cong id-right (comp-bilinear-ε₂ _)) (copair-cong (comp-bilinear-ε₂ _) id-right) ⟩
      copair in₁ εm +m copair εm in₂
    ≈⟨ copair-+ _ _ _ _ ⟩
      copair (in₁ +m εm) (εm +m in₂)
    ≈⟨ copair-cong +m-runit (homCM _ _ .+-lunit) ⟩
      copair in₁ in₂
    ≈⟨ copair-cong (≈-sym id-left) (≈-sym id-left) ⟩
      copair (id _ ∘ in₁) (id _ ∘ in₂)
    ≈⟨ copair-ext _ ⟩
      id _
    ∎ where open ≈-Reasoning isEquiv

------------------------------------------------------------------------------
-- Construct biproducts from products on a cmon-category
module cmon+product→biproduct {o m e}
         {𝒞 : Category o m e} (CM𝒞 : CMonEnriched 𝒞)
         {x y : 𝒞 .Category.obj} (P : Product 𝒞 x y) where

  open Category 𝒞
  open CMonEnriched CM𝒞
  open CommutativeMonoid
  open IsEquivalence

  open Product P

  -- Use the universal property of products to show that the pairing
  -- operation preserves zero and addition.
  pair-ε : ∀ {z} → pair εm εm ≈ εm {z} {prod}
  pair-ε =
    begin
      pair εm εm              ≈˘⟨ pair-cong (comp-bilinear-ε₂ p₁) (comp-bilinear-ε₂ p₂) ⟩
      pair (p₁ ∘ εm) (p₂ ∘ εm) ≈⟨ pair-ext εm ⟩
      εm                      ∎
    where open ≈-Reasoning isEquiv

  pair-+ : ∀ {z} (f₁ f₂ : z ⇒ x) (g₁ g₂ : z ⇒ y) →
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

  in₁ : x ⇒ prod
  in₁ = pair (id _) εm

  in₂ : y ⇒ prod
  in₂ = pair εm (id _)

  biproduct : Biproduct CM𝒞 x y
  biproduct .Biproduct.prod = prod
  biproduct .Biproduct.p₁ = p₁
  biproduct .Biproduct.p₂ = p₂
  biproduct .Biproduct.in₁ = in₁
  biproduct .Biproduct.in₂ = in₂
  biproduct .Biproduct.id-1 = pair-p₁ _ _
  biproduct .Biproduct.id-2 = pair-p₂ _ _
  biproduct .Biproduct.zero-1 = pair-p₁ _ _
  biproduct .Biproduct.zero-2 = pair-p₂ _ _
  biproduct .Biproduct.id-+ =
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

cmon+products→biproducts : ∀ {o m e}
  {𝒞 : Category o m e} (CM𝒞 : CMonEnriched 𝒞) (P : HasProducts 𝒞) →
  ∀ x y → Biproduct CM𝒞 x y
cmon+products→biproducts CM𝒞 P x y = biproduct
  where open cmon+product→biproduct CM𝒞 (HasProducts.getProduct P x y)


------------------------------------------------------------------------------
-- CMon-enrichment is inherited by functor categories
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

------------------------------------------------------------------------------
-- Generalising the above, cones made of zeros, or cones made by
-- addition, are preserved by going to limit cones.
open import functor

module _ {o m e o₂ m₂ e₂}
         {𝒞 : Category o m e} (CM𝒞 : CMonEnriched 𝒞)
         {𝒮 : Category o₂ m₂ e₂}
         (D : Functor 𝒮 𝒞)
         (L : Limit D)
  where

  open Category 𝒞
  open CMonEnriched CM𝒞
  open CommutativeMonoid
  open IsEquivalence
  open Limit L
  private
    module 𝒮𝒞Cmon = CMonEnriched (FunctorCat-cmon 𝒮 𝒞 CM𝒞)

  -- FIXME: Using the fact that const : 𝒞 ⇒ [ 𝒮 ⇒ 𝒞 ] is a
  -- Cmon-functor. Make this explicit.

  lambda-ε : ∀ {x} → lambda x 𝒮𝒞Cmon.εm ≈ εm {x} {apex}
  lambda-ε {x} = begin
      lambda x 𝒮𝒞Cmon.εm
    ≈˘⟨ lambda-cong (𝒮𝒞Cmon.comp-bilinear-ε₂ _) ⟩
      lambda x (cone functor.∘ 𝒮𝒞Cmon.εm)
    ≈⟨ lambda-cong (∘NT-cong (≃-isEquivalence .refl) (record { transf-eq = λ x → ≈-refl })) ⟩
      lambda x (cone functor.∘ constFmor εm)
    ≈⟨ lambda-ext _ ⟩
      εm
    ∎
    where open ≈-Reasoning isEquiv

  lambda-+ : ∀ {x} (α₁ α₂ : NatTrans (constF 𝒮 x) D) →
             (lambda x α₁ +m lambda x α₂) ≈ lambda x (α₁ 𝒮𝒞Cmon.+m α₂)
  lambda-+ {x} α₁ α₂ = begin
      lambda x α₁ +m lambda x α₂
    ≈˘⟨ lambda-ext _ ⟩
      lambda x (cone functor.∘ constFmor (lambda x α₁ +m lambda x α₂))
    ≈⟨ lambda-cong (∘NT-cong (≃-isEquivalence .refl) (record { transf-eq = λ x → ≈-refl })) ⟩
      lambda x (cone functor.∘ (constFmor (lambda x α₁) 𝒮𝒞Cmon.+m constFmor (lambda x α₂)))
    ≈⟨ lambda-cong (𝒮𝒞Cmon.comp-bilinear₂ _ _ _) ⟩
      lambda x ((cone functor.∘ constFmor (lambda x α₁)) 𝒮𝒞Cmon.+m (cone functor.∘ constFmor (lambda x α₂)))
    ≈⟨ lambda-cong (𝒮𝒞Cmon.homCM _ _ .+-cong (lambda-eval α₁) (lambda-eval α₂)) ⟩
      lambda x (α₁ 𝒮𝒞Cmon.+m α₂)
    ∎
    where open ≈-Reasoning isEquiv
