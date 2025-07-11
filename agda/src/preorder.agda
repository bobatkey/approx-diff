{-# OPTIONS --postfix-projections --safe --prop #-}

module preorder where

open import Level
open import prop
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import basics
open import prop-setoid using (IsEquivalence)

record Preorder : Set (suc 0ℓ) where
  no-eta-equality
  field
    Carrier      : Set
    _≤_          : Carrier → Carrier → Prop
    ≤-isPreorder : IsPreorder _≤_

  open IsPreorder ≤-isPreorder
    renaming (refl to ≤-refl; trans to ≤-trans)
    using (isEquivalence; _≃_) public
  open IsEquivalence isEquivalence
    renaming (refl to ≃-refl; sym to ≃-sym; trans to ≃-trans) public

module _ where
  open Preorder

  -- Monotone functions
  record _=>_ (A B : Preorder) : Set where
    open Preorder
    private
      module A = Preorder A
      module B = Preorder B
    field
      fun : A .Carrier → B .Carrier
      mono : ∀ {x₁} {x₂} → A ._≤_ x₁ x₂ → B ._≤_ (fun x₁) (fun x₂)

    resp-≃ : ∀ {x₁ x₂} → x₁ A.≃ x₂ → fun x₁ B.≃ fun x₂
    resp-≃ x₁≃x₂ .proj₁ = mono (x₁≃x₂ .proj₁)
    resp-≃ x₁≃x₂ .proj₂ = mono (x₁≃x₂ .proj₂)

module _ {A B : Preorder} where
  open _=>_
  private
    module A = Preorder A
    module B = Preorder B

  record _≃m_ (f g : A => B) : Prop where
    field
      eqfun : ∀ x → f .fun x B.≃ g .fun x

  open IsEquivalence
  open _≃m_

  ≃m-isEquivalence : IsEquivalence (_≃m_)
  ≃m-isEquivalence .refl .eqfun x = B.≃-refl
  ≃m-isEquivalence .sym e .eqfun x = B.≃-sym (e .eqfun x)
  ≃m-isEquivalence .trans e₁ e₂ .eqfun x = B.≃-trans (e₁ .eqfun x) (e₂ .eqfun x)

module _ where
  open Preorder
  open _=>_

  id : ∀ {A : Preorder} → A => A
  id .fun x = x
  id .mono x₁≤x₂ = x₁≤x₂

  _∘_ : ∀ {A B C : Preorder} → B => C → A => B → A => C
  (f ∘ g) .fun x = f .fun (g .fun x)
  (f ∘ g) .mono x₁≤x₂ = f .mono (g .mono x₁≤x₂)

  open _≃m_

  ∘-cong : ∀ {A B C : Preorder} {f₁ f₂ : B => C} {g₁ g₂ : A => B} → f₁ ≃m f₂ → g₁ ≃m g₂ → (f₁ ∘ g₁) ≃m (f₂ ∘ g₂)
  ∘-cong {A}{B}{C} {f₁ = f₁} f₁≃f₂ g₁≃g₂ .eqfun x =
    C .≃-trans (resp-≃ f₁ (g₁≃g₂ .eqfun x)) (f₁≃f₂ .eqfun _)

  id-left : ∀ {A B : Preorder} → {f : A => B} → (id ∘ f) ≃m f
  id-left {A} {B} .eqfun x = B .≃-refl

  id-right : ∀ {A B : Preorder} → {f : A => B} → (f ∘ id) ≃m f
  id-right {A} {B} .eqfun x = B .≃-refl

  assoc : ∀ {A B C D : Preorder} (f : C => D) (g : B => C) (h : A => B) → ((f ∘ g) ∘ h) ≃m (f ∘ (g ∘ h))
  assoc {D = D} f g h .eqfun x = D .≃-refl

module _ where
  open Preorder

  -- Unit preorder
  𝟙 : Preorder
  𝟙 .Carrier = Data.Unit.⊤
  𝟙 ._≤_ tt tt = ⊤
  𝟙 .≤-isPreorder .IsPreorder.refl = tt
  𝟙 .≤-isPreorder .IsPreorder.trans tt tt = tt

-- Lifting
data LCarrier (X : Set) : Set where
  bottom : LCarrier X
  <_>    : X → LCarrier X

module _ {X : Set} {_≤_ : X → X → Prop} (≤-isPreorder : IsPreorder _≤_) where

  _≤L_ : LCarrier X → LCarrier X → Prop
  bottom ≤L _     = ⊤
  < x > ≤L bottom = ⊥
  < x > ≤L < x' > = x ≤ x'

  open IsPreorder

  ≤L-isPreorder : IsPreorder _≤L_
  ≤L-isPreorder .refl {bottom} = tt
  ≤L-isPreorder .refl {< x >} = ≤-isPreorder .refl
  ≤L-isPreorder .trans {bottom} {bottom} {bottom} m₁ m₂ = tt
  ≤L-isPreorder .trans {bottom} {bottom} {< z >}  m₁ m₂ = tt
  ≤L-isPreorder .trans {bottom} {< y >}  {< z >}  m₁ m₂ = tt
  ≤L-isPreorder .trans {< x >}  {< y >}  {< z >}  m₁ m₂ = ≤-isPreorder .trans m₁ m₂

L : Preorder → Preorder
L X .Preorder.Carrier = LCarrier (X .Preorder.Carrier)
L X .Preorder._≤_ = _≤L_ (X .Preorder.≤-isPreorder)
L X .Preorder.≤-isPreorder = ≤L-isPreorder (X .Preorder.≤-isPreorder)

-- Binary products
module _ where
  open Preorder

  _×_ : Preorder → Preorder → Preorder
  (X × Y) .Carrier = Data.Product._×_ (X .Carrier) (Y .Carrier)
  (X × Y) ._≤_ (x₁ , y₁) (x₂ , y₂) = (X ._≤_ x₁ x₂) ∧ (Y ._≤_ y₁ y₂)
  (X × Y) .≤-isPreorder .IsPreorder.refl = (X .≤-refl) , (Y .≤-refl)
  (X × Y) .≤-isPreorder .IsPreorder.trans (x₁≤y₁ , x₂≤y₂) (y₁≤z₁ , y₂≤z₂) =
    (X .≤-trans x₁≤y₁ y₁≤z₁) , (Y .≤-trans x₂≤y₂ y₂≤z₂)

  ×-≃ : ∀ {X Y : Preorder} {x₁ x₂ : X .Carrier} {y₁ y₂ : Y .Carrier} →
        _≃_ X x₁ x₂ → _≃_ Y y₁ y₂ → _≃_ (X × Y) (x₁ , y₁) (x₂ , y₂)
  ×-≃ (x₁≤x₂ , x₂≤x₁) (y₁≤y₂ , y₂≤y₁) .proj₁ = x₁≤x₂ , y₁≤y₂
  ×-≃ (x₁≤x₂ , x₂≤x₁) (y₁≤y₂ , y₂≤y₁) .proj₂ = x₂≤x₁ , y₂≤y₁

-- Arbitrary products
module _ (I : Set) (A : I → Preorder) where
  open Preorder

  Π : Preorder
  Π .Carrier = ∀ i → A i .Carrier
  Π ._≤_ x₁ x₂ = ∀ i → A i ._≤_ (x₁ i) (x₂ i)
  Π .≤-isPreorder .IsPreorder.refl i = A i .≤-refl
  Π .≤-isPreorder .IsPreorder.trans x≤y y≤z i = A i .≤-trans (x≤y i) (y≤z i)
