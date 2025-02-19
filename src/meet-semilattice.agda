{-# OPTIONS --postfix-projections --safe --prop #-}

module meet-semilattice where

open import Level
open import Data.Product using (Σ; proj₁; proj₂; _,_)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import basics
open import prop renaming (_∧_ to _∧p_; ⊤ to ⊤p)
open import prop-setoid using (IsEquivalence)
open import preorder using (Preorder; _×_)

record MeetSemilattice (A : Preorder) : Set (suc 0ℓ) where
  no-eta-equality
  open Preorder public

  field
    _∧_       : A .Carrier → A .Carrier → A .Carrier
    ⊤         : A. Carrier
    ∧-isMeet  : IsMeet (A .≤-isPreorder) _∧_
    ⊤-isTop   : IsTop (A. ≤-isPreorder) ⊤

  open IsMeet ∧-isMeet
    renaming (assoc to ∧-assoc; ⟨_,_⟩ to ⟨_∧_⟩; mono to ∧-mono; comm to ∧-comm; cong to ∧-cong) public

  open IsTop ⊤-isTop public

  open IsMonoid (monoidOfMeet _ ∧-isMeet ⊤-isTop)
    using (interchange)
    renaming (lunit to ∧-lunit; runit to ∧-runit)
    public

module _ {A B : Preorder} where
  open Preorder
  private
    module A = Preorder A
    module B = Preorder B

  record _=>_ (X : MeetSemilattice A) (Y : MeetSemilattice B) : Set where
    open MeetSemilattice
    field
      func : A .Carrier → B .Carrier
      monotone : ∀ {x₁ x₂} → A ._≤_ x₁ x₂ → B ._≤_ (func x₁) (func x₂)
      ∧-preserving : ∀ {x x'} → B ._≤_ (Y ._∧_ (func x) (func x')) (func (X ._∧_ x x'))
      ⊤-preserving : B ._≤_ (Y .⊤) (func (X .⊤))

    resp-≃ : ∀ {x₁ x₂} → x₁ A.≃ x₂ → func x₁ B.≃ func x₂
    resp-≃ x₁≃x₂ .proj₁ = monotone (x₁≃x₂ .proj₁)
    resp-≃ x₁≃x₂ .proj₂ = monotone (x₁≃x₂ .proj₂)
  open _=>_

  record _≃m_ {X : MeetSemilattice A} {Y : MeetSemilattice B} (f g : X => Y) : Prop where
    field
      eqfunc : ∀ x → f .func x B.≃ g .func x

  open IsEquivalence
  open _≃m_

  ≃m-isEquivalence : ∀ {X Y} → IsEquivalence (_≃m_ {X} {Y})
  ≃m-isEquivalence .refl .eqfunc x = B.≃-refl
  ≃m-isEquivalence .sym e .eqfunc x = B.≃-sym (e .eqfunc x)
  ≃m-isEquivalence .trans e₁ e₂ .eqfunc x = B.≃-trans (e₁ .eqfunc x) (e₂ .eqfunc x)

------------------------------------------------------------------------------
module _ where
  open MeetSemilattice
  open _=>_

  id : ∀ {A}{X : MeetSemilattice A} → X => X
  id .func x = x
  id .monotone x₁≤x₂ = x₁≤x₂
  id {Α} .∧-preserving = Α .≤-refl
  id {Α} .⊤-preserving = Α .≤-refl

  _∘_ : ∀ {A B C}{X : MeetSemilattice A}{Y : MeetSemilattice B}{Z : MeetSemilattice C} →
        Y => Z → X => Y → X => Z
  (f ∘ g) .func x = f .func (g .func x)
  (f ∘ g) .monotone x₁≤x₂ = f .monotone (g .monotone x₁≤x₂)
  _∘_ {C = C} f g .∧-preserving =
    C .≤-trans (f .∧-preserving) (f .monotone (g .∧-preserving))
  _∘_ {C = C} f g .⊤-preserving =
    C .≤-trans (f .⊤-preserving) (f .monotone (g .⊤-preserving))

  open _≃m_

  ∘-cong : ∀ {A B C}{X : MeetSemilattice A}{Y : MeetSemilattice B}{Z : MeetSemilattice C}
             {f₁ f₂ : Y => Z} {g₁ g₂ : X => Y} →
             f₁ ≃m f₂ → g₁ ≃m g₂ → (f₁ ∘ g₁) ≃m (f₂ ∘ g₂)
  ∘-cong {A}{B}{C} {f₁ = f₁} f₁≃f₂ g₁≃g₂ .eqfunc x =
    C .≃-trans (resp-≃ f₁ (g₁≃g₂ .eqfunc x)) (f₁≃f₂ .eqfunc _)

  id-left : ∀ {A B}{X : MeetSemilattice A}{Y : MeetSemilattice B} →
            {f : X => Y} → (id ∘ f) ≃m f
  id-left {A} {B} .eqfunc x = B .≃-refl

  id-right : ∀ {A B}{X : MeetSemilattice A}{Y : MeetSemilattice B} →
            {f : X => Y} → (f ∘ id) ≃m f
  id-right {A} {B} .eqfunc x = B .≃-refl

  assoc : ∀ {A B C D}
            {W : MeetSemilattice A}
            {X : MeetSemilattice B}
            {Y : MeetSemilattice C}
            {Z : MeetSemilattice D}
            (f : Y => Z) (g : X => Y) (h : W => X) →
            ((f ∘ g) ∘ h) ≃m (f ∘ (g ∘ h))
  assoc {D = D} f g h .eqfunc x = D .≃-refl

  -- Additive structure
  --
  -- FIXME: this is true of any monoids: generalise!
  module _ {A B}{X : MeetSemilattice A}{Y : MeetSemilattice B} where
    private
      module B = Preorder B
      module Y = MeetSemilattice Y

    εm : X => Y
    εm .func x = Y.⊤
    εm .monotone _ = B.≤-refl
    εm .∧-preserving = Y.∧-lunit .proj₁
    εm .⊤-preserving = B.≤-refl

    _+m_ : X => Y → X => Y → X => Y
    (f +m g) .func x = f .func x Y.∧ g .func x
    (f +m g) .monotone x₁≤x₂ = Y.∧-mono (f .monotone x₁≤x₂) (g .monotone x₁≤x₂)
    (f +m g) .∧-preserving =
      B.≤-trans (Y.interchange Y.∧-comm .proj₁)
                (Y.∧-mono (f .∧-preserving) (g .∧-preserving))
    (f +m g) .⊤-preserving =
      B.≤-trans (Y.∧-lunit .proj₂) (Y.∧-mono (f .⊤-preserving) (g .⊤-preserving))

    +m-cong : ∀ {f₁ f₂ g₁ g₂ : X => Y} → f₁ ≃m f₂ → g₁ ≃m g₂ → (f₁ +m g₁) ≃m (f₂ +m g₂)
    +m-cong f₁≃f₂ g₁≃g₂ .eqfunc x = Y.∧-cong (f₁≃f₂ .eqfunc x) (g₁≃g₂ .eqfunc x)

    +m-comm : ∀ {f g} → (f +m g) ≃m (g +m f)
    +m-comm .eqfunc x .proj₁ = Y.∧-comm
    +m-comm .eqfunc x .proj₂ = Y.∧-comm

    +m-assoc : ∀ {f g h} → ((f +m g) +m h) ≃m (f +m (g +m h))
    +m-assoc .eqfunc x = Y.∧-assoc

    +m-lunit : ∀ {f} → (εm +m f) ≃m f
    +m-lunit .eqfunc x = Y.∧-lunit



------------------------------------------------------------------------------
-- Big Products
module _ (I : Set) {A : I → Preorder} (X : (i : I) → MeetSemilattice (A i)) where
  open MeetSemilattice
  open _=>_

  Π-preorder : Preorder
  Π-preorder = preorder.Π I A

  Π : MeetSemilattice Π-preorder
  Π ._∧_ x₁ x₂ i = X i ._∧_ (x₁ i) (x₂ i)
  Π .⊤ i = X i .⊤
  Π .∧-isMeet .IsMeet.π₁ i = X i .∧-isMeet .IsMeet.π₁
  Π .∧-isMeet .IsMeet.π₂ i = X i .∧-isMeet .IsMeet.π₂
  Π .∧-isMeet .IsMeet.⟨_,_⟩ x≤y x≤z i = X i .∧-isMeet .IsMeet.⟨_,_⟩ (x≤y i) (x≤z i)
  Π .⊤-isTop .IsTop.≤-top i = X i .⊤-isTop .IsTop.≤-top

  proj-Π : (i : I) → Π => X i
  proj-Π i .func x = x i
  proj-Π i .monotone x₁≤x₂ = x₁≤x₂ i
  proj-Π i .∧-preserving = A i .≤-refl
  proj-Π i .⊤-preserving = A i .≤-refl

  lambda-Π : ∀ {B} {W : MeetSemilattice B} → (W=>X : ∀ i → W => X i) → W => Π
  lambda-Π W=>X .func w i = W=>X i .func w
  lambda-Π W=>X .monotone w₁≤w₂ i = W=>X i .monotone w₁≤w₂
  lambda-Π W=>X .∧-preserving i = W=>X i .∧-preserving
  lambda-Π W=>X .⊤-preserving i = W=>X i .⊤-preserving

------------------------------------------------------------------------------
module _ where
  open MeetSemilattice
  open _=>_

  𝟙 : MeetSemilattice preorder.𝟙
  𝟙 ._∧_ tt tt = tt
  𝟙 .⊤ = tt
  𝟙 .∧-isMeet .IsMeet.π₁ = tt
  𝟙 .∧-isMeet .IsMeet.π₂ = tt
  𝟙 .∧-isMeet .IsMeet.⟨_,_⟩ tt tt = tt
  𝟙 .⊤-isTop .IsTop.≤-top = tt

  terminal : ∀ {A}{X : MeetSemilattice A} → X => 𝟙
  terminal .func _ = tt
  terminal .monotone _ = tt
  terminal .∧-preserving = tt
  terminal .⊤-preserving = tt

  open _=>_
  open _≃m_

  terminal-unique : ∀ {A}(X : MeetSemilattice A) → (f g : X => 𝟙) → f ≃m g
  terminal-unique X f g .eqfunc x = tt , tt

------------------------------------------------------------------------------
-- Biproducts
module _ where
  open Preorder
  open MeetSemilattice
  open _=>_
  open _≃m_

  _⊕_ : ∀ {A B} → MeetSemilattice A → MeetSemilattice B → MeetSemilattice (A × B)
  (X ⊕ Y) ._∧_ (x₁ , y₁) (x₂ , y₂) = (X ._∧_ x₁ x₂) , (Y ._∧_ y₁ y₂)
  (X ⊕ Y) .⊤ = (X .⊤) , (Y .⊤)
  (X ⊕ Y) .∧-isMeet .IsMeet.π₁ = X .∧-isMeet .IsMeet.π₁ , Y .∧-isMeet .IsMeet.π₁
  (X ⊕ Y) .∧-isMeet .IsMeet.π₂ = X .∧-isMeet .IsMeet.π₂ , Y .∧-isMeet .IsMeet.π₂
  (X ⊕ Y) .∧-isMeet .IsMeet.⟨_,_⟩ (x₁≤y₁ , x₂≤y₂) (x₁≤z₁ , x₂≤z₂) =
    X .∧-isMeet .IsMeet.⟨_,_⟩ x₁≤y₁ x₁≤z₁ , Y .∧-isMeet .IsMeet.⟨_,_⟩ x₂≤y₂ x₂≤z₂
  (X ⊕ Y) .⊤-isTop .IsTop.≤-top = X .⊤-isTop .IsTop.≤-top , Y .⊤-isTop .IsTop.≤-top

  project₁ : ∀ {A B} {X : MeetSemilattice A} {Y : MeetSemilattice B} → (X ⊕ Y) => X
  project₁ .func = proj₁
  project₁ .monotone = proj₁
  project₁ {A = A} .∧-preserving = A .≤-refl
  project₁ {A = A} .⊤-preserving = A .≤-refl

  project₂ : ∀ {A B} {X : MeetSemilattice A} {Y : MeetSemilattice B} → (X ⊕ Y) => Y
  project₂ .func = proj₂
  project₂ .monotone = proj₂
  project₂ {B = B} .∧-preserving = B .≤-refl
  project₂ {B = B} .⊤-preserving = B .≤-refl

  ⟨_,_⟩ : ∀ {A B C} {W : MeetSemilattice A} {X : MeetSemilattice B} {Y : MeetSemilattice C} →
          W => X → W => Y → W => (X ⊕ Y)
  ⟨_,_⟩ f g .func w = f .func w , g .func w
  ⟨_,_⟩ f g .monotone w₁≤w₂ = (f .monotone w₁≤w₂) , (g .monotone w₁≤w₂)
  ⟨_,_⟩ f g .∧-preserving = (f .∧-preserving) , (g .∧-preserving)
  ⟨_,_⟩ f g .⊤-preserving = (f .⊤-preserving) , (g .⊤-preserving)

  ⟨⟩-cong : ∀ {A B C}{W : MeetSemilattice A} {X : MeetSemilattice B} {Y : MeetSemilattice C} →
           {f₁ f₂ : W => X} {g₁ g₂ : W => Y} →
           f₁ ≃m f₂ → g₁ ≃m g₂ → ⟨ f₁ , g₁ ⟩ ≃m ⟨ f₂ , g₂ ⟩
  ⟨⟩-cong f₁≈f₂ g₁≈g₂ .eqfunc x .proj₁ .proj₁ = f₁≈f₂ .eqfunc x .proj₁
  ⟨⟩-cong f₁≈f₂ g₁≈g₂ .eqfunc x .proj₁ .proj₂ = g₁≈g₂ .eqfunc x .proj₁
  ⟨⟩-cong f₁≈f₂ g₁≈g₂ .eqfunc x .proj₂ .proj₁ = f₁≈f₂ .eqfunc x .proj₂
  ⟨⟩-cong f₁≈f₂ g₁≈g₂ .eqfunc x .proj₂ .proj₂ = g₁≈g₂ .eqfunc x .proj₂

  pair-p₁ : ∀ {A B C}{X : MeetSemilattice A} {Y : MeetSemilattice B} {Z : MeetSemilattice C}
            (f : X => Y) (g : X => Z) →
            (project₁ ∘ ⟨ f , g ⟩) ≃m f
  pair-p₁ {B = B} f g .eqfunc x = B .≃-refl

  pair-p₂ : ∀ {A B C}{X : MeetSemilattice A} {Y : MeetSemilattice B} {Z : MeetSemilattice C}
            (f : X => Y) (g : X => Z) →
            (project₂ ∘ ⟨ f , g ⟩) ≃m g
  pair-p₂ {C = C} f g .eqfunc x = C .≃-refl

  pair-ext : ∀ {A B C}{X : MeetSemilattice A} {Y : MeetSemilattice B} {Z : MeetSemilattice C}
             (f : X => (Y ⊕ Z)) →
             ⟨ project₁ ∘ f , project₂ ∘ f ⟩ ≃m f
  pair-ext {B = B} {C = C} f .eqfunc x = (B × C) .≃-refl

  inject₁ : ∀ {A B} {X : MeetSemilattice A} {Y : MeetSemilattice B} → X => (X ⊕ Y)
  inject₁ {Y = Y} .func x = x , Y .⊤
  inject₁ {B = B} .monotone x₁≤x₂ = x₁≤x₂ , B .≤-refl
  inject₁ {A = A} .∧-preserving .proj₁ = A .≤-refl
  inject₁ {Y = Y} .∧-preserving .proj₂ = Y .⊤-isTop .IsTop.≤-top
  inject₁ {A = A}{B = B} .⊤-preserving = A .≤-refl , B .≤-refl

  inject₂ : ∀ {A B} {X : MeetSemilattice A} {Y : MeetSemilattice B} → Y => (X ⊕ Y)
  inject₂ {X = X} .func y = X .⊤ , y
  inject₂ {A = A} .monotone y₁≤y₂ = A .≤-refl , y₁≤y₂
  inject₂ {X = X} .∧-preserving .proj₁ = X .⊤-isTop .IsTop.≤-top
  inject₂ {B = B} .∧-preserving .proj₂ = B .≤-refl
  inject₂ {A = A}{B = B} .⊤-preserving = A .≤-refl , B .≤-refl

  [_,_] : ∀ {A B C}{X : MeetSemilattice A}{Y : MeetSemilattice B}{Z : MeetSemilattice C} →
    X => Z → Y => Z → (X ⊕ Y) => Z
  [_,_] {Z = Z} f g .func (x , y) = Z ._∧_ (f .func x) (g .func y)
  [_,_] {Z = Z} f g .monotone (x₁≤x₂ , y₁≤y₂) =
    mono (f .monotone x₁≤x₂) (g .monotone y₁≤y₂)
    where open IsMeet (Z .∧-isMeet)
  [_,_] {C = C}{Z = Z} f g .∧-preserving {x , y} {x' , y'} =
    C .≤-trans (Z.interchange Z.∧-comm .proj₁)
               (Z.∧-mono (f .∧-preserving) (g .∧-preserving))
      where module Z = MeetSemilattice Z
  [_,_] {Z = Z} f g .⊤-preserving = ⟨ (f .⊤-preserving) , (g .⊤-preserving) ⟩Z
    where open IsMeet (Z .∧-isMeet) renaming (⟨_,_⟩ to ⟨_,_⟩Z)

------------------------------------------------------------------------------
-- Lifting
module _ where
  open preorder using (LCarrier; <_>; bottom)
  open MeetSemilattice
  open _=>_

  L : ∀ {A} → MeetSemilattice A → MeetSemilattice (preorder.L A)
  L X ._∧_ bottom _ = bottom
  L X ._∧_ < x > bottom = bottom
  L X ._∧_ < x > < y > = < X ._∧_ x y >
  L X .⊤ = < X .⊤ >
  L X .∧-isMeet .IsMeet.π₁ {bottom} {y} = tt
  L X .∧-isMeet .IsMeet.π₁ {< x >} {bottom} = tt
  L X .∧-isMeet .IsMeet.π₁ {< x >} {< x₁ >} = X .∧-isMeet .IsMeet.π₁
  L X .∧-isMeet .IsMeet.π₂ {bottom} {bottom} = tt
  L X .∧-isMeet .IsMeet.π₂ {bottom} {< x >} = tt
  L X .∧-isMeet .IsMeet.π₂ {< x >} {bottom} = tt
  L X .∧-isMeet .IsMeet.π₂ {< x >} {< x₁ >} = X .∧-isMeet .IsMeet.π₂
  L X .∧-isMeet .IsMeet.⟨_,_⟩ {bottom} {bottom} {z} x≤y x≤z = tt
  L X .∧-isMeet .IsMeet.⟨_,_⟩ {bottom} {< y >}  {bottom} x≤y x≤z = tt
  L X .∧-isMeet .IsMeet.⟨_,_⟩ {bottom} {< y >}  {< z >} x≤y x≤z = tt
  L X .∧-isMeet .IsMeet.⟨_,_⟩ {< x >}  {< y >}  {< z >} x≤y x≤z =
    X .∧-isMeet .IsMeet.⟨_,_⟩ x≤y x≤z
  L X .⊤-isTop .IsTop.≤-top {bottom} = tt
  L X .⊤-isTop .IsTop.≤-top {< x >} = X .⊤-isTop .IsTop.≤-top

  L-unit : ∀ {A}{X : MeetSemilattice A} → X => L X
  L-unit .func x = < x >
  L-unit .monotone x₁≤x₂ = x₁≤x₂
  L-unit {A} .∧-preserving = A .≤-refl
  L-unit {A} .⊤-preserving = A .≤-refl

  L-join : ∀ {A}{X : MeetSemilattice A} → L (L X) => L X
  L-join .func bottom = bottom
  L-join .func < bottom > = bottom
  L-join .func < < x > > = < x >
  L-join .monotone {bottom}     {bottom}     x₁≤x₂ = tt
  L-join .monotone {bottom}     {< bottom >} x₁≤x₂ = tt
  L-join .monotone {bottom}     {< < x > >}  x₁≤x₂ = tt
  L-join .monotone {< bottom >} {< bottom >} x₁≤x₂ = tt
  L-join .monotone {< bottom >} {< < x > >}  x₁≤x₂ = tt
  L-join .monotone {< < x > >}  {< < y > >}  x₁≤x₂ = x₁≤x₂
  L-join .∧-preserving {bottom} {bottom} = tt
  L-join .∧-preserving {bottom} {< x >} = tt
  L-join .∧-preserving {< bottom >} {bottom} = tt
  L-join .∧-preserving {< < x > >} {bottom} = tt
  L-join .∧-preserving {< bottom >} {< x₁ >} = tt
  L-join .∧-preserving {< < x > >} {< bottom >} = tt
  L-join {A} .∧-preserving {< < x > >} {< < x₁ > >} = A .≤-refl
  L-join {A} .⊤-preserving = A .≤-refl

  L-map : ∀ {A B}{X : MeetSemilattice A}{Y : MeetSemilattice B} → X => Y → L X => L Y
  L-map f .func bottom = bottom
  L-map f .func < x > = < f .func x >
  L-map f .monotone {bottom} {bottom} x₁≤x₂ = tt
  L-map f .monotone {bottom} {< x₂ >} x₁≤x₂ = tt
  L-map f .monotone {< x₁ >} {< x₂ >} x₁≤x₂ = f .monotone x₁≤x₂
  L-map f .∧-preserving {bottom} {x'} = tt
  L-map f .∧-preserving {< x >} {bottom} = tt
  L-map f .∧-preserving {< x >} {< x₁ >} = f .∧-preserving
  L-map f .⊤-preserving = f .⊤-preserving

  L-strength : ∀ {A B}{X : MeetSemilattice A}{Y : MeetSemilattice B} →
               (X ⊕ L Y) => L (X ⊕ Y)
  L-strength .func (x , bottom) = bottom
  L-strength .func (x , < y >) = < x , y >
  L-strength .monotone {x₁ , bottom} {x₂ , bottom} (x₁≤x₂ , tt) = tt
  L-strength .monotone {x₁ , bottom} {x₂ , < y >}  (x₁≤x₂ , tt) = tt
  L-strength .monotone {x₁ , < y₁ >} {x₂ , < y₂ >} (x₁≤x₂ , y₁≤y₂) = x₁≤x₂ , y₁≤y₂
  L-strength .∧-preserving {x , bottom} {x' , y'} = tt
  L-strength .∧-preserving {x , < x₁ >} {x' , bottom} = tt
  L-strength {A}{B} .∧-preserving {x , < x₁ >} {x' , < x₂ >} = A .≤-refl , B .≤-refl
  L-strength {A}{B} .⊤-preserving = A .≤-refl , B .≤-refl
