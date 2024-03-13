{-# OPTIONS --postfix-projections --allow-unsolved-metas --without-K #-}

module join-semilattice where

open import Level
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Relation.Binary using (IsEquivalence; Reflexive)
open import basics

record JoinSemilattice : Set (suc 0ℓ) where
  no-eta-equality
  field
    Carrier      : Set
    _≤_          : Carrier → Carrier → Set
    _∨_          : Carrier → Carrier → Carrier
    ⊥            : Carrier
    ≤-isPreorder : IsPreorder _≤_
    ∨-isJoin     : IsJoin ≤-isPreorder _∨_
    ⊥-isBottom   : IsBottom ≤-isPreorder ⊥

  ∨-⊥-isMonoid : IsMonoid ≤-isPreorder _∨_ ⊥
  ∨-⊥-isMonoid = monoidOfJoin _ ∨-isJoin ⊥-isBottom

  open IsPreorder ≤-isPreorder renaming (refl to ≤-refl; trans to ≤-trans) public
  open IsEquivalence (isEquivalenceOf ≤-isPreorder) renaming (refl to ≃-refl; sym to ≃-sym) public
  open IsBottom ⊥-isBottom public
  open IsJoin ∨-isJoin public hiding ([_,_])
    renaming (cong to ∨-cong'; mono to ∨-mono; idem to ∨-idem; comm to ∨-comm'; assoc to ∨-assoc')

record _=>_ (X Y : JoinSemilattice) : Set where
  open JoinSemilattice
  open IsPreorder (X .JoinSemilattice.≤-isPreorder) renaming (_≃_ to _≃₁_)
  open IsPreorder (Y .JoinSemilattice.≤-isPreorder) renaming (_≃_ to _≃₂_)
  field
    func : X .Carrier → Y .Carrier
    monotone : ∀ {x₁ x₂} → X ._≤_ x₁ x₂ → Y ._≤_ (func x₁) (func x₂)
    ∨-preserving : ∀ {x x'} → Y ._≤_ (func (X ._∨_ x x')) (Y ._∨_ (func x) (func x'))
    ⊥-preserving : Y ._≤_ (func (X .⊥)) (Y .⊥)

  cong : ∀ {x x'} → x ≃₁ x' → func x ≃₂ func x'
  cong (x≤x' , _) .proj₁ = monotone x≤x'
  cong (_ , x'≤x) .proj₂ = monotone x'≤x

open _=>_

record _≃m_ {X Y : JoinSemilattice} (f g : X => Y) : Set where
  open IsPreorder (Y .JoinSemilattice.≤-isPreorder)
  field
    eqfunc : ∀ x → f .func x ≃ g .func x

open JoinSemilattice

id : ∀ {X} → X => X
id .func x = x
id .monotone x≤x' = x≤x'
id {X} .∨-preserving = X .≤-refl
id {X} .⊥-preserving = X .≤-refl

_∘_ : ∀ {X Y Z} → Y => Z → X => Y → X => Z
(f ∘ g) .func x = f .func (g .func x)
(f ∘ g) .monotone x≤x' = f .monotone (g .monotone x≤x')
_∘_ {X}{Y}{Z} f g .∨-preserving = Z .≤-trans (f .monotone (g .∨-preserving)) (f .∨-preserving)
_∘_ {X}{Y}{Z} f g .⊥-preserving = Z .≤-trans (f .monotone (g .⊥-preserving)) (f .⊥-preserving)

-- constant (left zero) morphisms
⊥-map : ∀ {X Y} → X => Y
⊥-map {X}{Y} .func _ = Y .⊥
⊥-map {X}{Y} .monotone _ = ≤-refl Y
⊥-map {X}{Y} .∨-preserving = ∨-idem Y .proj₂
⊥-map {X}{Y} .⊥-preserving = Y .≤-refl

-- FIXME: ∨-map

------------------------------------------------------------------------------
-- One element semilattice, for use when there are no approximations
𝟙 : JoinSemilattice
𝟙 .Carrier = ⊤
𝟙 ._≤_ tt tt = ⊤
𝟙 ._∨_ tt tt = tt
𝟙 .⊥ = tt
𝟙 .≤-isPreorder .IsPreorder.refl = tt
𝟙 .≤-isPreorder .IsPreorder.trans tt tt = tt
𝟙 .∨-isJoin .IsJoin.inl = tt
𝟙 .∨-isJoin .IsJoin.inr = tt
𝟙 .∨-isJoin .IsJoin.[_,_] tt tt = tt
𝟙 .⊥-isBottom .IsBottom.≤-bottom = tt

-- this is a zero object (both initial and terminal)

------------------------------------------------------------------------------
-- Lifting

data LCarrier (X : Set) : Set where
  bottom : LCarrier X
  <_>    : X → LCarrier X

-- Add a new bottom element to a finite join semilattice
L : JoinSemilattice → JoinSemilattice
L X .Carrier = LCarrier (X .Carrier)
L X ._≤_ bottom bottom = ⊤
L X ._≤_ bottom < _ >  = ⊤
L X ._≤_ < _ >  bottom = 𝟘
L X ._≤_ < x > < y >   = X ._≤_ x y
L X ._∨_ bottom bottom = bottom
L X ._∨_ < x >  bottom = < x >
L X ._∨_ bottom < y >  = < y >
L X ._∨_ < x >  < y >  = < X ._∨_ x y >
L X .⊥ = bottom
L X .≤-isPreorder .IsPreorder.refl {bottom} = tt
L X .≤-isPreorder .IsPreorder.refl {< x >} = ≤-refl X
L X .≤-isPreorder .IsPreorder.trans {bottom} {bottom} {bottom} m₁ m₂ = tt
L X .≤-isPreorder .IsPreorder.trans {bottom} {bottom} {< z >}  m₁ m₂ = tt
L X .≤-isPreorder .IsPreorder.trans {bottom} {< y >}  {< z >}  m₁ m₂ = tt
L X .≤-isPreorder .IsPreorder.trans {< x >}  {< y >}  {< z >}  m₁ m₂ =
  X .≤-isPreorder .IsPreorder.trans m₁ m₂
L X .∨-isJoin .IsJoin.inl {bottom} {bottom} = tt
L X .∨-isJoin .IsJoin.inl {bottom} {< x >}  = tt
L X .∨-isJoin .IsJoin.inl {< x >}  {bottom} = ≤-refl X
L X .∨-isJoin .IsJoin.inl {< x >}  {< y >}  = X .∨-isJoin .IsJoin.inl
L X .∨-isJoin .IsJoin.inr {bottom} {bottom} = tt
L X .∨-isJoin .IsJoin.inr {bottom} {< x >}  = ≤-refl X
L X .∨-isJoin .IsJoin.inr {< x >}  {bottom} = tt
L X .∨-isJoin .IsJoin.inr {< x >}  {< y >}  = X .∨-isJoin .IsJoin.inr
L X .∨-isJoin .IsJoin.[_,_] {bottom}{bottom}{bottom} m₁ m₂ = tt
L X .∨-isJoin .IsJoin.[_,_] {bottom}{bottom}{< z >}  m₁ m₂ = tt
L X .∨-isJoin .IsJoin.[_,_] {bottom}{< y >} {z}      m₁ m₂ = m₂
L X .∨-isJoin .IsJoin.[_,_] {< x >} {bottom}{z}      m₁ m₂ = m₁
L X .∨-isJoin .IsJoin.[_,_] {< x >} {< y >} {< z >}  m₁ m₂ = X .∨-isJoin .IsJoin.[_,_] m₁ m₂
L X .⊥-isBottom .IsBottom.≤-bottom {bottom} = tt
L X .⊥-isBottom .IsBottom.≤-bottom {< x >} = tt

L-func : ∀ {X Y} → X => Y → L X => L Y
L-func m .func bottom = bottom
L-func m .func < x > = < m .func x >
L-func {X} {Y} m .monotone {bottom} {bottom} _ = tt
L-func {X} {Y} m .monotone {bottom} {< _ >} _ = tt
L-func m .monotone {< _ >} {bottom} ()
L-func m .monotone {< _ >} {< _ >} x₁≤x₂ = m .monotone x₁≤x₂
L-func m .∨-preserving {bottom} {bottom} = tt
L-func {X}{Y} m .∨-preserving {bottom} {< _ >} = Y .≤-refl
L-func {X}{Y} m .∨-preserving {< x >} {bottom} = Y .≤-refl
L-func m .∨-preserving {< _ >} {< _ >} = m .∨-preserving
L-func m .⊥-preserving = tt

-- Lifting is /not/ a monad: L-unit is not ⊥-preserving!
{-
L-unit : ∀ {X} → X => L X
L-unit .func x = < x >
L-unit .monotone x≤x' = x≤x'
L-unit {X} .join-preserving = ≃-refl X
L-unit .⊥-preserving = {!!}
-}

L-join : ∀ {X} → L (L X) => L X
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
L-join {X} .∨-preserving {bottom} {< < x > >} = X .≤-refl
L-join .∨-preserving {< bottom >} {bottom} = tt
L-join {X} .∨-preserving {< < _ > >} {bottom} = X .≤-refl
L-join .∨-preserving {< bottom >} {< bottom >} = tt
L-join {X} .∨-preserving {< bottom >} {< < x > >} = X .≤-refl
L-join {X} .∨-preserving {< < _ > >} {< bottom >} = X .≤-refl
L-join {X} .∨-preserving {< < _ > >} {< < _ > >} = X .≤-refl
L-join .⊥-preserving = tt

-- Lifting is a comonad in preorders with a bottom:
L-counit : ∀ {X} → L X => X
L-counit {X} .func bottom = X .⊥
L-counit .func < x > = x
L-counit {X} .monotone {bottom} _ = X .≤-bottom
L-counit {X} .monotone {< _ >} {< _ >} x≤x' = x≤x'
L-counit {X} .∨-preserving {bottom} {bottom} = ∨-idem X .proj₂
L-counit {X} .∨-preserving {bottom} {< _ >} = IsMonoid.lunit (∨-⊥-isMonoid X) .proj₂
L-counit {X} .∨-preserving {< _ >} {bottom} = IsMonoid.runit (∨-⊥-isMonoid X) .proj₂
L-counit {X} .∨-preserving {< _ >} {< _ >} = X .≤-refl
L-counit {X} .⊥-preserving = X .≤-refl

L-dup : ∀ {X} → L X => L (L X)
L-dup .func bottom = bottom
L-dup .func < x > = < < x > >
L-dup .monotone {bottom} {bottom} _ = tt
L-dup .monotone {bottom} {< _ >} _ = tt
L-dup .monotone {< _ >} {< _ >} x≤x' = x≤x'
L-dup {X} .∨-preserving {bottom} {bottom} = tt
L-dup {X} .∨-preserving {bottom} {< _ >} = X .≤-refl
L-dup {X} .∨-preserving {< _ >} {bottom} = X .≤-refl
L-dup {X} .∨-preserving {< _ >} {< _ >} = X .≤-refl
L-dup {X} .⊥-preserving = tt

L-coassoc : ∀ {X} → (L-func L-dup ∘ L-dup) ≃m (L-dup ∘ L-dup {X})
L-coassoc ._≃m_.eqfunc bottom .proj₁ = tt
L-coassoc ._≃m_.eqfunc bottom .proj₂ = tt
L-coassoc {X} ._≃m_.eqfunc < x > = X. ≃-refl

L-unit1 : ∀ {X} → (L-counit ∘ L-dup) ≃m id {L X}
L-unit1 ._≃m_.eqfunc bottom .proj₁ = tt
L-unit1 ._≃m_.eqfunc bottom .proj₂ = tt
L-unit1 {X} ._≃m_.eqfunc < x > = X. ≃-refl

L-unit2 : ∀ {X} → (L-func L-counit ∘ L-dup) ≃m id {L X}
L-unit2 ._≃m_.eqfunc bottom .proj₁ = tt
L-unit2 ._≃m_.eqfunc bottom .proj₂ = tt
L-unit2 {X} ._≃m_.eqfunc < x > = X. ≃-refl

------------------------------------------------------------------------------
-- Set-wide direct sums of JoinSemilattices
module _ (I : Set) (X : I → JoinSemilattice) where

  data FormalJoin : Set where
    bot  : FormalJoin
    el   : (i : I) → X i .Carrier → FormalJoin
    join : FormalJoin → FormalJoin → FormalJoin

  data _≤f_ : FormalJoin → FormalJoin → Set where
    ≤f-refl    : ∀ {j} → j ≤f j
    ≤f-trans   : ∀ {j₁ j₂ j₃} → j₁ ≤f j₂ → j₂ ≤f j₃ → j₁ ≤f j₃
    ≤f-el-mono : ∀ i {x₁ x₂} → X i ._≤_ x₁ x₂ → el i x₁ ≤f el i x₂
    ≤f-el-bot  : ∀ i → el i (X i .⊥) ≤f bot
    ≤f-el-join : ∀ i {x₁ x₂} → el i (X i ._∨_ x₁ x₂) ≤f join (el i x₁) (el i x₂)
    ≤f-bot     : ∀ {j} → bot ≤f j
    ≤f-inl     : ∀ {j₁ j₂} → j₁ ≤f join j₁ j₂
    ≤f-inr     : ∀ {j₁ j₂} → j₂ ≤f join j₁ j₂
    ≤f-case    : ∀ {j₁ j₂ j₃} → j₁ ≤f j₃ → j₂ ≤f j₃ → join j₁ j₂ ≤f j₃

  ⨁ : JoinSemilattice
  ⨁ .Carrier = FormalJoin
  ⨁ ._≤_ = _≤f_
  ⨁ ._∨_ = join
  ⨁ .⊥ = bot
  ⨁ .≤-isPreorder .IsPreorder.refl = ≤f-refl
  ⨁ .≤-isPreorder .IsPreorder.trans = ≤f-trans
  ⨁ .∨-isJoin .IsJoin.inl = ≤f-inl
  ⨁ .∨-isJoin .IsJoin.inr = ≤f-inr
  ⨁ .∨-isJoin .IsJoin.[_,_] = ≤f-case
  ⨁ .⊥-isBottom .IsBottom.≤-bottom = ≤f-bot

  inj-⨁ : (i : I) → X i => ⨁
  inj-⨁ i .func x = el i x
  inj-⨁ i .monotone = ≤f-el-mono i
  inj-⨁ i .∨-preserving = ≤f-el-join i
  inj-⨁ i .⊥-preserving = ≤f-el-bot i

  module _ (Z : JoinSemilattice) (X=>Z : ∀ i → X i => Z) where
    module Z = JoinSemilattice Z

    open IsJoin (Z .∨-isJoin)

    elim-⨁-func : ⨁ .Carrier → Z .Carrier
    elim-⨁-func bot = Z.⊥
    elim-⨁-func (el i x) = X=>Z i .func x
    elim-⨁-func (join j₁ j₂) = elim-⨁-func j₁ Z.∨ elim-⨁-func j₂

    elim-⨁-func-monotone : ∀ {j₁ j₂} → j₁ ≤f j₂ → elim-⨁-func j₁ Z.≤ elim-⨁-func j₂
    elim-⨁-func-monotone ≤f-refl = Z.≤-refl
    elim-⨁-func-monotone (≤f-trans j₁≤j₂ j₂≤j₃) = Z.≤-trans (elim-⨁-func-monotone j₁≤j₂) (elim-⨁-func-monotone j₂≤j₃)
    elim-⨁-func-monotone (≤f-el-mono i x₁≤x₂) = X=>Z i .monotone x₁≤x₂
    elim-⨁-func-monotone (≤f-el-bot i) = X=>Z i .⊥-preserving
    elim-⨁-func-monotone (≤f-el-join i) = {!   !}
    elim-⨁-func-monotone ≤f-bot = Z .≤-bottom
    elim-⨁-func-monotone ≤f-inl = Z .inl
    elim-⨁-func-monotone ≤f-inr = Z .inr
    elim-⨁-func-monotone (≤f-case j₁≤j₃ j₂≤j₃) =
      [ elim-⨁-func-monotone j₁≤j₃ , elim-⨁-func-monotone j₂≤j₃ ]

    elim-⨁ : ⨁ => Z
    elim-⨁ .func = elim-⨁-func
    elim-⨁ .monotone = elim-⨁-func-monotone
    elim-⨁ .∨-preserving = Z .≤-refl
    elim-⨁ .⊥-preserving = Z .≤-refl

------------------------------------------------------------------------------
-- Biproducts
_⊕_ : JoinSemilattice → JoinSemilattice → JoinSemilattice
(X ⊕ Y) .Carrier = X .Carrier × Y .Carrier
(X ⊕ Y) ._≤_ (x₁ , y₁) (x₂ , y₂) = (X ._≤_ x₁ x₂) × (Y ._≤_ y₁ y₂)
(X ⊕ Y) ._∨_ (x₁ , y₁) (x₂ , y₂) = (X ._∨_ x₁ x₂) , (Y ._∨_ y₁ y₂)
(X ⊕ Y) .⊥ = X .⊥ , Y .⊥
(X ⊕ Y) .≤-isPreorder .IsPreorder.refl = ≤-refl X , ≤-refl Y
(X ⊕ Y) .≤-isPreorder .IsPreorder.trans (x₁≤y₁ , x₂≤y₂) (y₁≤z₁ , y₂≤z₂) =
  X .≤-isPreorder .IsPreorder.trans x₁≤y₁ y₁≤z₁ ,
  Y .≤-isPreorder .IsPreorder.trans x₂≤y₂ y₂≤z₂
(X ⊕ Y) .∨-isJoin .IsJoin.inl = X .∨-isJoin .IsJoin.inl , Y .∨-isJoin .IsJoin.inl
(X ⊕ Y) .∨-isJoin .IsJoin.inr = X .∨-isJoin .IsJoin.inr , Y .∨-isJoin .IsJoin.inr
(X ⊕ Y) .∨-isJoin .IsJoin.[_,_] (x₁≤z₁ , y₁≤z₂) (x₂≤z₁ , y₂≤z₂) =
  X .∨-isJoin .IsJoin.[_,_] x₁≤z₁ x₂≤z₁ ,
  Y .∨-isJoin .IsJoin.[_,_] y₁≤z₂ y₂≤z₂
(X ⊕ Y) .⊥-isBottom .IsBottom.≤-bottom = ≤-bottom X , ≤-bottom Y

-- Product bits:
project₁ : ∀ {X Y} → (X ⊕ Y) => X
project₁ .func = proj₁
project₁ .monotone = proj₁
project₁ {X} .∨-preserving = X .≤-refl
project₁ {X} .⊥-preserving = X .≤-refl

project₂ : ∀ {X Y} → (X ⊕ Y) => Y
project₂ .func = proj₂
project₂ .monotone = proj₂
project₂ {X}{Y} .∨-preserving = Y .≤-refl
project₂ {X}{Y} .⊥-preserving = Y .≤-refl

⟨_,_⟩ : ∀ {X Y Z} → X => Y → X => Z → X => (Y ⊕ Z)
⟨ f , g ⟩ .func x = f .func x , g .func x
⟨ f , g ⟩ .monotone x≤x' = f .monotone x≤x' , g .monotone x≤x'
⟨ f , g ⟩ .∨-preserving = f .∨-preserving , g .∨-preserving
⟨ f , g ⟩ .⊥-preserving = f .⊥-preserving , g . ⊥-preserving

-- Coproduct bits:
inject₁ : ∀ {X Y} → X => (X ⊕ Y)
inject₁ {X}{Y} .func x = x , Y .⊥
inject₁ {X}{Y} .monotone x≤x' = x≤x' , Y .≤-refl
inject₁ {X}{Y} .∨-preserving = X .≤-refl , ∨-idem Y .proj₂
inject₁ {X}{Y} .⊥-preserving = X .≤-refl , Y .≤-refl

inject₂ : ∀ {X Y} → Y => (X ⊕ Y)
inject₂ {X}{Y} .func y = X .⊥ , y
inject₂ {X}{Y} .monotone y≤y' = ≤-refl X , y≤y'
inject₂ {X}{Y} .∨-preserving = ∨-idem X .proj₂ , Y .≤-refl
inject₂ {X}{Y} .⊥-preserving = X .≤-refl , Y .≤-refl

[_,_] : ∀ {X Y Z} → X => Z → Y => Z → (X ⊕ Y) => Z
[_,_] {X}{Y}{Z} f g .func (x , y) = Z ._∨_ (f .func x) (g .func y)
[_,_] {X}{Y}{Z} f g .monotone (x₁≤x₁' , x₂≤x₂') =
  IsJoin.mono (Z .∨-isJoin) (f .monotone x₁≤x₁') (g .monotone x₂≤x₂')
[_,_] {X}{Y}{Z} f g .∨-preserving {(x₁ , y₁)}{(x₂ , y₂)} =
  -- redo with inequality reasoning
  Z .≤-trans
    (∨-mono Z (f .∨-preserving) (g .∨-preserving))
  (Z .≤-trans
    (∨-assoc' Z .proj₁)
  (Z .≤-trans
    (∨-mono Z (Z .≤-refl)
      (Z .≤-trans
        (Z .≃-sym (∨-assoc' Z) .proj₁)
      (Z .≤-trans
        (∨-mono Z (∨-comm' Z .proj₁) (Z .≤-refl))
        (∨-assoc' Z .proj₁))))
    (Z .≃-sym (∨-assoc' Z) .proj₁)))
[_,_] {X}{Y}{Z} f g .⊥-preserving = Z[ f .⊥-preserving , g .⊥-preserving ]
  where open IsJoin (Z .∨-isJoin) renaming ([_,_] to Z[_,_])

-- Binary biproduct properties
proj₁-inverts-inj₁ : ∀ {X Y} → (project₁ {X} {Y} ∘ inject₁) ≃m id
proj₁-inverts-inj₁ {X} ._≃m_.eqfunc x = ≃-refl X

proj₂-inverts-inj₂ : ∀ {X Y} → (project₁ {X} {Y} ∘ inject₁) ≃m id
proj₂-inverts-inj₂ {X} ._≃m_.eqfunc x = ≃-refl X

proj₁-zeroes-inj₂ : ∀ {X Y} → (project₁ {X} {Y} ∘ inject₂) ≃m ⊥-map
proj₁-zeroes-inj₂ {X}{Y} ._≃m_.eqfunc x = ≃-refl X

proj₂-zeroes-inj₁ : ∀ {X Y} → (project₂ {X} {Y} ∘ inject₁) ≃m ⊥-map
proj₂-zeroes-inj₁ {X}{Y} ._≃m_.eqfunc x = ≃-refl Y
