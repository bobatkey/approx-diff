{-# OPTIONS --postfix-projections --safe --without-K #-}

module join-semilattice where

open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Level
open import Relation.Binary using (IsEquivalence)
open import basics
open import preorder using (Preorder; _×_)

record JoinSemilattice (A : Preorder) : Set (suc 0ℓ) where
  no-eta-equality
  open Preorder public

  field
    _∨_          : A .Carrier → A .Carrier → A .Carrier
    ⊥            : A .Carrier
    ∨-isJoin     : IsJoin (A .≤-isPreorder) _∨_
    ⊥-isBottom   : IsBottom (A .≤-isPreorder) ⊥

  open IsEquivalence (isEquivalenceOf (A .≤-isPreorder)) renaming (refl to ≃-refl; sym to ≃-sym) public

module _ {A B : Preorder} where
  open Preorder

  record _=>_ (X : JoinSemilattice A) (Y : JoinSemilattice B) : Set where
    open JoinSemilattice
    field
      func : A .Carrier → B .Carrier
      monotone : ∀ {x₁ x₂} → A ._≤_ x₁ x₂ → B ._≤_ (func x₁) (func x₂)
      ∨-preserving : ∀ {x x'} → B ._≤_ (func (X ._∨_ x x')) (Y ._∨_ (func x) (func x'))
      ⊥-preserving : B ._≤_ (func (X .⊥)) (Y .⊥)

  record _≃m_ {X : JoinSemilattice A} {Y : JoinSemilattice B} (f g : X => Y) : Set where
    open _=>_
    field
      eqfunc : ∀ x → _≃_ B (f .func x) (g .func x)

module _ where
  open JoinSemilattice
  open _=>_

  id : ∀ {A}{X : JoinSemilattice A} → X => X
  id .func x = x
  id .monotone x≤x' = x≤x'
  id {X} .∨-preserving = X .≤-refl
  id {X} .⊥-preserving = X .≤-refl

  _∘_ : ∀ {A B C}{X : JoinSemilattice A}{Y : JoinSemilattice B}{Z : JoinSemilattice C} → Y => Z → X => Y → X => Z
  (f ∘ g) .func x = f .func (g .func x)
  (f ∘ g) .monotone x≤x' = f .monotone (g .monotone x≤x')
  _∘_ {C = C} f g .∨-preserving = C .≤-trans (f .monotone (g .∨-preserving)) (f .∨-preserving)
  _∘_ {C = C} f g .⊥-preserving = C .≤-trans (f .monotone (g .⊥-preserving)) (f .⊥-preserving)

  ⊥-map : ∀ {A}{B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → X => Y
  ⊥-map {Y = Y} .func y = Y .⊥
  ⊥-map {B = B} .monotone _ = B .≤-refl
  ⊥-map {Y = Y} .∨-preserving = IsJoin.idem (Y .∨-isJoin) .proj₂
  ⊥-map {B = B} .⊥-preserving = B .≤-refl

------------------------------------------------------------------------------
-- One element semilattice, for use when there are no approximations
module _ where
  open JoinSemilattice

  𝟙 : JoinSemilattice preorder.𝟙
  𝟙 ._∨_ tt tt = tt
  𝟙 .⊥ = tt
  𝟙 .∨-isJoin .IsJoin.inl = tt
  𝟙 .∨-isJoin .IsJoin.inr = tt
  𝟙 .∨-isJoin .IsJoin.[_,_] tt tt = tt
  𝟙 .⊥-isBottom .IsBottom.≤-bottom = tt

  -- this is a zero object (both initial and terminal)
  initial : ∀ {A}{X : JoinSemilattice A} → 𝟙 => X
  initial = ⊥-map

------------------------------------------------------------------------------
-- Lifting
module _ where
  open preorder using (LCarrier; <_>; bottom)
  open JoinSemilattice
  open _=>_

  L : ∀ {A} → JoinSemilattice A → JoinSemilattice (preorder.L A)
  L X ._∨_ bottom bottom = bottom
  L X ._∨_ < x >  bottom = < x >
  L X ._∨_ bottom < y >  = < y >
  L X ._∨_ < x >  < y >  = < X ._∨_ x y >
  L X .⊥ = bottom
  L X .∨-isJoin .IsJoin.inl {bottom} {bottom} = tt
  L X .∨-isJoin .IsJoin.inl {bottom} {< x >}  = tt
  L {A} X .∨-isJoin .IsJoin.inl {< x >}  {bottom} = A .≤-refl
  L X .∨-isJoin .IsJoin.inl {< x >}  {< y >}  = X .∨-isJoin .IsJoin.inl
  L X .∨-isJoin .IsJoin.inr {bottom} {bottom} = tt
  L {A} X .∨-isJoin .IsJoin.inr {bottom} {< x >}  = A. ≤-refl
  L X .∨-isJoin .IsJoin.inr {< x >}  {bottom} = tt
  L X .∨-isJoin .IsJoin.inr {< x >}  {< y >}  = X .∨-isJoin .IsJoin.inr
  L X .∨-isJoin .IsJoin.[_,_] {bottom}{bottom}{bottom} m₁ m₂ = tt
  L X .∨-isJoin .IsJoin.[_,_] {bottom}{bottom}{< z >}  m₁ m₂ = tt
  L X .∨-isJoin .IsJoin.[_,_] {bottom}{< y >} {z}      m₁ m₂ = m₂
  L X .∨-isJoin .IsJoin.[_,_] {< x >} {bottom}{z}      m₁ m₂ = m₁
  L X .∨-isJoin .IsJoin.[_,_] {< x >} {< y >} {< z >}  m₁ m₂ = X .∨-isJoin .IsJoin.[_,_] m₁ m₂
  L X .⊥-isBottom .IsBottom.≤-bottom {bottom} = tt
  L X .⊥-isBottom .IsBottom.≤-bottom {< x >} = tt

  L-func : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → X => Y → L X => L Y
  L-func m .func bottom = bottom
  L-func m .func < x > = < m .func x >
  L-func m .monotone {bottom} {bottom} _ = tt
  L-func m .monotone {bottom} {< _ >} _ = tt
  L-func m .monotone {< _ >} {bottom} ()
  L-func m .monotone {< _ >} {< _ >} x₁≤x₂ = m .monotone x₁≤x₂
  L-func m .∨-preserving {bottom} {bottom} = tt
  L-func {B = B} m .∨-preserving {bottom} {< _ >} = B .≤-refl
  L-func {B = B} m .∨-preserving {< x >} {bottom} = B .≤-refl
  L-func m .∨-preserving {< _ >} {< _ >} = m .∨-preserving
  L-func m .⊥-preserving = tt

  -- Lifting is /not/ a monad: L-unit is not ⊥-preserving

  L-join : ∀ {A}{X : JoinSemilattice A} → L (L X) => L X
  L-join .func bottom = bottom
  L-join .func < bottom > = bottom
  L-join .func < < x > > = < x >
  L-join .monotone {bottom} {bottom} _ = tt
  L-join .monotone {bottom} {< bottom >} _ = tt
  L-join .monotone {bottom} {< < _ > >} _ = tt
  L-join .monotone {< bottom >} {< bottom >} _ = tt
  L-join .monotone {< bottom >} {< < _ > >} _ = tt
  L-join .monotone {< < _ > >} {< < _ > >} x≤x' = x≤x'
  L-join .∨-preserving {bottom} {bottom} = tt
  L-join .∨-preserving {bottom} {< bottom >} = tt
  L-join {A} .∨-preserving {bottom} {< < x > >} = A .≤-refl
  L-join .∨-preserving {< bottom >} {bottom} = tt
  L-join {A} .∨-preserving {< < _ > >} {bottom} = A .≤-refl
  L-join .∨-preserving {< bottom >} {< bottom >} = tt
  L-join {A} .∨-preserving {< bottom >} {< < x > >} = A .≤-refl
  L-join {A} .∨-preserving {< < _ > >} {< bottom >} = A .≤-refl
  L-join {A} .∨-preserving {< < _ > >} {< < _ > >} = A .≤-refl
  L-join .⊥-preserving = tt

  -- Lifting is a comonad in preorders with a bottom:
  L-counit : ∀ {A}{X : JoinSemilattice A} → L X => X
  L-counit {X = X} .func bottom = X .⊥
  L-counit .func < x > = x
  L-counit {X = X} .monotone {bottom} _ = IsBottom.≤-bottom (X .⊥-isBottom)
  L-counit .monotone {< _ >} {< _ >} x≤x' = x≤x'
  L-counit {X = X} .∨-preserving {bottom} {bottom} = IsJoin.idem (X .∨-isJoin) .proj₂
  L-counit {X = X} .∨-preserving {bottom} {< _ >} =
    IsMonoid.lunit (monoidOfJoin _ (X .∨-isJoin) (X .⊥-isBottom)) .proj₂
  L-counit {X = X} .∨-preserving {< _ >} {bottom} =
    IsMonoid.runit (monoidOfJoin _ (X .∨-isJoin) (X .⊥-isBottom)) .proj₂
  L-counit {A} .∨-preserving {< _ >} {< _ >} = A .≤-refl
  L-counit {A} .⊥-preserving = A .≤-refl

  L-dup : ∀ {A}{X : JoinSemilattice A} → L X => L (L X)
  L-dup .func bottom = bottom
  L-dup .func < x > = < < x > >
  L-dup .monotone {bottom} {bottom} _ = tt
  L-dup .monotone {bottom} {< _ >} _ = tt
  L-dup .monotone {< _ >} {< _ >} x≤x' = x≤x'
  L-dup .∨-preserving {bottom} {bottom} = tt
  L-dup {A} .∨-preserving {bottom} {< _ >} = A .≤-refl
  L-dup {A} .∨-preserving {< _ >} {bottom} = A .≤-refl
  L-dup {A} .∨-preserving {< _ >} {< _ >} = A .≤-refl
  L-dup .⊥-preserving = tt

  L-coassoc : ∀ {A}{X : JoinSemilattice A} → (L-func L-dup ∘ L-dup) ≃m (L-dup ∘ L-dup {X = X})
  L-coassoc ._≃m_.eqfunc bottom .proj₁ = tt
  L-coassoc ._≃m_.eqfunc bottom .proj₂ = tt
  L-coassoc {X = X} ._≃m_.eqfunc < x > = X. ≃-refl

  L-unit1 : ∀ {A}{X : JoinSemilattice A} → (L-counit ∘ L-dup) ≃m id {X = L X}
  L-unit1 ._≃m_.eqfunc bottom .proj₁ = tt
  L-unit1 ._≃m_.eqfunc bottom .proj₂ = tt
  L-unit1 {X = X} ._≃m_.eqfunc < x > = X. ≃-refl

  L-unit2 : ∀ {A}{X : JoinSemilattice A} → (L-func L-counit ∘ L-dup) ≃m id {X = L X}
  L-unit2 ._≃m_.eqfunc bottom .proj₁ = tt
  L-unit2 ._≃m_.eqfunc bottom .proj₂ = tt
  L-unit2 {X = X} ._≃m_.eqfunc < x > = X. ≃-refl

------------------------------------------------------------------------------
-- Set-wide direct sums of JoinSemilattices
module _ (I : Set) (A : I -> Preorder) (X : (i : I) → JoinSemilattice (A i)) where
  open JoinSemilattice
  open _=>_

  data FormalJoin : Set where
    bot  : FormalJoin
    el   : (i : I) → A i .Carrier → FormalJoin
    join : FormalJoin → FormalJoin → FormalJoin

  data _≤f_ : FormalJoin → FormalJoin → Set where
    ≤f-refl    : ∀ {j} → j ≤f j
    ≤f-trans   : ∀ {j₁ j₂ j₃} → j₁ ≤f j₂ → j₂ ≤f j₃ → j₁ ≤f j₃
    ≤f-el-mono : ∀ i {x₁ x₂} → A i ._≤_ x₁ x₂ → el i x₁ ≤f el i x₂
    ≤f-el-bot  : ∀ i → el i (X i .⊥) ≤f bot
    ≤f-el-join : ∀ i {x₁ x₂} → el i (X i ._∨_ x₁ x₂) ≤f join (el i x₁) (el i x₂)
    ≤f-bot     : ∀ {j} → bot ≤f j
    ≤f-inl     : ∀ {j₁ j₂} → j₁ ≤f join j₁ j₂
    ≤f-inr     : ∀ {j₁ j₂} → j₂ ≤f join j₁ j₂
    ≤f-case    : ∀ {j₁ j₂ j₃} → j₁ ≤f j₃ → j₂ ≤f j₃ → join j₁ j₂ ≤f j₃

  ⨁-preorder : Preorder
  ⨁-preorder .Carrier = FormalJoin
  ⨁-preorder ._≤_ = _≤f_
  ⨁-preorder .≤-isPreorder .IsPreorder.refl = ≤f-refl
  ⨁-preorder .≤-isPreorder .IsPreorder.trans = ≤f-trans

  ⨁ : JoinSemilattice ⨁-preorder
  ⨁ ._∨_ = join
  ⨁ .⊥ = bot
  ⨁ .∨-isJoin .IsJoin.inl = ≤f-inl
  ⨁ .∨-isJoin .IsJoin.inr = ≤f-inr
  ⨁ .∨-isJoin .IsJoin.[_,_] = ≤f-case
  ⨁ .⊥-isBottom .IsBottom.≤-bottom = ≤f-bot

  inj-⨁ : (i : I) → X i => ⨁
  inj-⨁ i .func x = el i x
  inj-⨁ i .monotone = ≤f-el-mono i
  inj-⨁ i .∨-preserving = ≤f-el-join i
  inj-⨁ i .⊥-preserving = ≤f-el-bot i

  module _ {B} (Z : JoinSemilattice B) (X=>Z : ∀ i → X i => Z) where
    open IsJoin (Z .∨-isJoin)
    open IsBottom (Z .⊥-isBottom)

    elim-⨁-func : ⨁-preorder .Carrier → B .Carrier
    elim-⨁-func bot = Z .⊥
    elim-⨁-func (el i x) = X=>Z i .func x
    elim-⨁-func (join j₁ j₂) = Z ._∨_ (elim-⨁-func j₁) (elim-⨁-func j₂)

    elim-⨁-func-monotone : ∀ {j₁ j₂} → j₁ ≤f j₂ → B ._≤_ (elim-⨁-func j₁) (elim-⨁-func j₂)
    elim-⨁-func-monotone ≤f-refl = B .≤-refl
    elim-⨁-func-monotone (≤f-trans j₁≤j₂ j₂≤j₃) = B .≤-trans (elim-⨁-func-monotone j₁≤j₂) (elim-⨁-func-monotone j₂≤j₃)
    elim-⨁-func-monotone (≤f-el-mono i x₁≤x₂) = X=>Z i .monotone x₁≤x₂
    elim-⨁-func-monotone (≤f-el-bot i) = X=>Z i .⊥-preserving
    elim-⨁-func-monotone (≤f-el-join i) = X=>Z i .∨-preserving
    elim-⨁-func-monotone ≤f-bot = ≤-bottom
    elim-⨁-func-monotone ≤f-inl = inl
    elim-⨁-func-monotone ≤f-inr = inr
    elim-⨁-func-monotone (≤f-case j₁≤j₃ j₂≤j₃) =
      [ elim-⨁-func-monotone j₁≤j₃ , elim-⨁-func-monotone j₂≤j₃ ]

    elim-⨁ : ⨁ => Z
    elim-⨁ .func = elim-⨁-func
    elim-⨁ .monotone = elim-⨁-func-monotone
    elim-⨁ .∨-preserving = B .≤-refl
    elim-⨁ .⊥-preserving = B .≤-refl

------------------------------------------------------------------------------
-- Biproducts
module _ where
  open JoinSemilattice
  open _=>_

  _⊕_ : ∀ {A B} → JoinSemilattice A → JoinSemilattice B → JoinSemilattice (A × B)
  (X ⊕ Y) ._∨_ (x₁ , y₁) (x₂ , y₂) = (X ._∨_ x₁ x₂) , (Y ._∨_ y₁ y₂)
  (X ⊕ Y) .⊥ = X .⊥ , Y .⊥
  (X ⊕ Y) .∨-isJoin .IsJoin.inl = X .∨-isJoin .IsJoin.inl , Y .∨-isJoin .IsJoin.inl
  (X ⊕ Y) .∨-isJoin .IsJoin.inr = X .∨-isJoin .IsJoin.inr , Y .∨-isJoin .IsJoin.inr
  (X ⊕ Y) .∨-isJoin .IsJoin.[_,_] (x₁≤z₁ , y₁≤z₂) (x₂≤z₁ , y₂≤z₂) =
    X .∨-isJoin .IsJoin.[_,_] x₁≤z₁ x₂≤z₁ ,
    Y .∨-isJoin .IsJoin.[_,_] y₁≤z₂ y₂≤z₂
  (X ⊕ Y) .⊥-isBottom .IsBottom.≤-bottom = IsBottom.≤-bottom (X .⊥-isBottom) , IsBottom.≤-bottom (Y .⊥-isBottom)

  -- Product bits:
  project₁ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → (X ⊕ Y) => X
  project₁ .func = proj₁
  project₁ .monotone = proj₁
  project₁ {A} .∨-preserving = A .≤-refl
  project₁ {A} .⊥-preserving = A .≤-refl

  project₂ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → (X ⊕ Y) => Y
  project₂ .func = proj₂
  project₂ .monotone = proj₂
  project₂ {B = B} .∨-preserving = B .≤-refl
  project₂ {B = B} .⊥-preserving = B .≤-refl

  ⟨_,_⟩ : ∀ {A B C}{X : JoinSemilattice A}{Y : JoinSemilattice B}{Z : JoinSemilattice C} → X => Y → X => Z → X => (Y ⊕ Z)
  ⟨ f , g ⟩ .func x = f .func x , g .func x
  ⟨ f , g ⟩ .monotone x≤x' = f .monotone x≤x' , g .monotone x≤x'
  ⟨ f , g ⟩ .∨-preserving = f .∨-preserving , g .∨-preserving
  ⟨ f , g ⟩ .⊥-preserving = f .⊥-preserving , g . ⊥-preserving

  -- Coproduct bits:
  inject₁ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → X => (X ⊕ Y)
  inject₁ {Y = Y} .func x = x , Y .⊥
  inject₁ {B = B} .monotone x≤x' = x≤x' , B .≤-refl
  inject₁ {A}{Y = Y} .∨-preserving = A .≤-refl , IsJoin.idem (Y .∨-isJoin) .proj₂
  inject₁ {X}{Y} .⊥-preserving = X .≤-refl , Y .≤-refl

  inject₂ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → Y => (X ⊕ Y)
  inject₂ {X = X} .func y = X .⊥ , y
  inject₂ {A} .monotone y≤y' = A. ≤-refl , y≤y'
  inject₂ {B = B}{X = X} .∨-preserving = IsJoin.idem (X .∨-isJoin) .proj₂ , B .≤-refl
  inject₂ {A}{B} .⊥-preserving = A .≤-refl , B .≤-refl

  [_,_] : ∀ {A B C}{X : JoinSemilattice A}{Y : JoinSemilattice B}{Z : JoinSemilattice C} → X => Z → Y => Z → (X ⊕ Y) => Z
  [_,_] {Z = Z} f g .func (x , y) = Z ._∨_ (f .func x) (g .func y)
  [_,_] {Z = Z} f g .monotone (x₁≤x₁' , x₂≤x₂') =
    IsJoin.mono (Z .∨-isJoin) (f .monotone x₁≤x₁') (g .monotone x₂≤x₂')
  [_,_] {C = C}{Z = Z} f g .∨-preserving {(x₁ , y₁)}{(x₂ , y₂)} =
    C .≤-trans (IsJoin.mono (Z .∨-isJoin) (f .∨-preserving) (g .∨-preserving))
               (interchange (IsJoin.sym (Z .∨-isJoin)))
    where open IsMonoid (monoidOfJoin (C .≤-isPreorder) (Z .∨-isJoin) (Z .⊥-isBottom))
  [_,_] {Z = Z} f g .⊥-preserving = Z[ f .⊥-preserving , g .⊥-preserving ]
    where open IsJoin (Z .∨-isJoin) renaming ([_,_] to Z[_,_])

  -- Biproduct properties
  proj₁-inverts-inj₁ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → (project₁ {X = X}{Y} ∘ inject₁) ≃m id
  proj₁-inverts-inj₁ {X = X} ._≃m_.eqfunc x = ≃-refl X

  proj₂-inverts-inj₂ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → (project₁ {X = X}{Y} ∘ inject₁) ≃m id
  proj₂-inverts-inj₂ {X = X} ._≃m_.eqfunc x = ≃-refl X

  proj₁-zeroes-inj₂ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → (project₁ {X = X}{Y} ∘ inject₂) ≃m ⊥-map
  proj₁-zeroes-inj₂ {X = X} ._≃m_.eqfunc x = ≃-refl X

  proj₂-zeroes-inj₁ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → (project₂ {X = X}{Y} ∘ inject₁) ≃m ⊥-map
  proj₂-zeroes-inj₁ {X = X}{Y} ._≃m_.eqfunc x = ≃-refl Y
