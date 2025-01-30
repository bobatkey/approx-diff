{-# OPTIONS --postfix-projections --prop --safe #-}

module galois where

open import Level
open import Data.Product using (_,_; proj₁; proj₂)
open import prop
open import basics
open import prop-setoid
  using (IsEquivalence)
  renaming (_⇒_ to _⇒s_)
open import preorder
  hiding (𝟙)
open import categories
open import meet-semilattice
  using (MeetSemilattice)
  renaming (_=>_ to _=>M_; _≃m_ to _≃M_; id to idM; _∘_ to _∘M_;
            _⊕_ to _⊕M_;
            ≃m-isEquivalence to ≃M-isEquivalence)
open import join-semilattice
  using (JoinSemilattice)
  renaming (_=>_ to _=>J_; _≃m_ to _≃J_; id to idJ; _∘_ to _∘J_;
            _⊕_ to _⊕J_;
            ≃m-isEquivalence to ≃J-isEquivalence)

-- The category of bounded lattices and Galois connections between
-- them.
--
-- We define the objects as being partially ordered sets that have a
-- meet structure and a join structure. The morphisms are pairs of
-- adjoint monotone functions.
--
-- Fam(Galois) is our basic setting for approximation. Objects are
-- sets indexing bounded lattices of approximations. Morphisms are
-- functions between the sets, equipped with a forward derivative and
-- a reverse derivative. The reverse derivative takes

record Obj : Set (suc 0ℓ) where
  field
    carrier : Preorder
    meets   : MeetSemilattice carrier
    joins   : JoinSemilattice carrier
  open Preorder carrier public
open Obj

record _⇒g_ (X Y : Obj) : Set where
  private
    module X = Obj X
    module Y = Obj Y
  field
    fwd : X .meets =>M Y .meets
    bwd : Y .joins =>J X .joins
    bwd⊣fwd : ∀ {x y} → y Y.≤ (fwd ._=>M_.func x) ⇔ (bwd ._=>J_.func y) X.≤ x

  -- FIXME: preservation of meets and joins comes for free! but then
  -- it would be harder to reuse the defined morphisms from before.
open _⇒g_

record _≃g_ {X Y : Obj} (f g : X ⇒g Y) : Prop where
  field
    fwd-eq : f .fwd ≃M g .fwd
    bwd-eq : f .bwd ≃J g .bwd
open _≃g_

open IsEquivalence

≃g-isEquivalence : ∀ {X Y} → IsEquivalence (_≃g_ {X} {Y})
≃g-isEquivalence .refl .fwd-eq = ≃M-isEquivalence .refl
≃g-isEquivalence .refl .bwd-eq = ≃J-isEquivalence .refl
≃g-isEquivalence .sym e .fwd-eq = ≃M-isEquivalence .sym (e .fwd-eq)
≃g-isEquivalence .sym e .bwd-eq = ≃J-isEquivalence .sym (e .bwd-eq)
≃g-isEquivalence .trans e₁ e₂ .fwd-eq = ≃M-isEquivalence .trans (e₁ .fwd-eq) (e₂ .fwd-eq)
≃g-isEquivalence .trans e₁ e₂ .bwd-eq = ≃J-isEquivalence .trans (e₁ .bwd-eq) (e₂ .bwd-eq)

idg : (X : Obj) → X ⇒g X
idg X .fwd = idM
idg X .bwd = idJ
idg X .bwd⊣fwd = refl-⇔

_∘g_ : ∀ {X Y Z : Obj} → Y ⇒g Z → X ⇒g Y → X ⇒g Z
(f ∘g g) .fwd = f .fwd ∘M g .fwd
(f ∘g g) .bwd = g .bwd ∘J f .bwd
(f ∘g g) .bwd⊣fwd = trans-⇔ (f .bwd⊣fwd) (g .bwd⊣fwd)

∘g-cong : ∀ {X Y Z}{f₁ f₂ : Y ⇒g Z}{g₁ g₂ : X ⇒g Y} → f₁ ≃g f₂ → g₁ ≃g g₂ → (f₁ ∘g g₁) ≃g (f₂ ∘g g₂)
∘g-cong f₁≈f₂ g₁≈g₂ .fwd-eq = meet-semilattice.∘-cong (f₁≈f₂ .fwd-eq) (g₁≈g₂ .fwd-eq)
∘g-cong f₁≈f₂ g₁≈g₂ .bwd-eq = join-semilattice.∘-cong (g₁≈g₂ .bwd-eq) (f₁≈f₂ .bwd-eq)

module _ where

  open Category

  cat : Category (suc 0ℓ) 0ℓ 0ℓ
  cat .obj = Obj
  cat ._⇒_ = _⇒g_
  cat ._≈_ = _≃g_
  cat .isEquiv = ≃g-isEquivalence
  cat .id = idg
  cat ._∘_ = _∘g_
  cat .∘-cong = ∘g-cong
  cat .id-left .fwd-eq = meet-semilattice.id-left
  cat .id-left .bwd-eq = join-semilattice.id-right
  cat .id-right .fwd-eq = meet-semilattice.id-right
  cat .id-right .bwd-eq = join-semilattice.id-left
  cat .assoc f g h .fwd-eq = meet-semilattice.assoc (f .fwd) (g .fwd) (h .fwd)
  cat .assoc f g h .bwd-eq =
    ≃J-isEquivalence .sym (join-semilattice.assoc (h .bwd) (g .bwd) (f .bwd))

  -- FIXME: this category is additive

-- Terminal (FIXME: and initial)
module _ where
  open HasTerminal

  𝟙 : Obj
  𝟙 .carrier = preorder.𝟙
  𝟙 .meets = meet-semilattice.𝟙
  𝟙 .joins = join-semilattice.𝟙

  to-𝟙 : ∀ X → X ⇒g 𝟙
  to-𝟙 X .fwd = meet-semilattice.terminal
  to-𝟙 X .bwd = join-semilattice.initial
  to-𝟙 X .bwd⊣fwd .proj₁ tt =
    X .joins .JoinSemilattice.⊥-isBottom .IsBottom.≤-bottom
  to-𝟙 X .bwd⊣fwd .proj₂ _ = tt

  terminal : HasTerminal cat
  terminal .witness = 𝟙
  terminal .terminal-mor = to-𝟙
  terminal .terminal-unique X f g .fwd-eq = meet-semilattice.terminal-unique _ _ _
  terminal .terminal-unique X f g .bwd-eq = join-semilattice.initial-unique _ _ _

-- This category has binary products (FIXME: and biproducts)
module _ where

  open HasProducts

  _⊗_ : Obj → Obj → Obj
  (X ⊗ Y) .carrier = X .carrier × Y .carrier
  (X ⊗ Y) .meets = X .meets ⊕M Y .meets
  (X ⊗ Y) .joins = X .joins ⊕J Y .joins

  open JoinSemilattice

  products : HasProducts cat
  products .prod = _⊗_
  products .p₁ .fwd = meet-semilattice.project₁
  products .p₁ .bwd = join-semilattice.inject₁
  products .p₁ {X} {Y} .bwd⊣fwd {x , y} {x'} .proj₁ x'≤x .proj₁ = x'≤x
  products .p₁ {X} {Y} .bwd⊣fwd {x , y} {x'} .proj₁ x'≤x .proj₂ = ≤-bottom
    where open IsBottom (Y .joins .⊥-isBottom)
  products .p₁ {X} {Y} .bwd⊣fwd {x , y} {x'} .proj₂ = proj₁
  products .p₂ .fwd = meet-semilattice.project₂
  products .p₂ .bwd = join-semilattice.inject₂
  products .p₂ {X} {Y} .bwd⊣fwd {x , y} {y'} .proj₁ y'≤y .proj₁ = ≤-bottom
    where open IsBottom (X .joins .⊥-isBottom)
  products .p₂ {X} {Y} .bwd⊣fwd {x , y} {y'} .proj₁ y'≤y .proj₂ = y'≤y
  products .p₂ {X} {Y} .bwd⊣fwd {x , y} {y'} .proj₂ = proj₂
  products .pair f g .fwd = meet-semilattice.⟨ f .fwd , g .fwd ⟩
  products .pair f g .bwd = join-semilattice.[ f .bwd , g .bwd ]
  products .pair {X} {Y} {Z} f g .bwd⊣fwd {x} {y , z} .proj₁ (y≤fx , z≤gx) =
    [ f .bwd⊣fwd .proj₁ y≤fx , g .bwd⊣fwd .proj₁ z≤gx ]
    where open IsJoin (X .joins .∨-isJoin)
  products .pair {X} {Y} {Z} f g .bwd⊣fwd {x} {y , z} .proj₂ fy∨gz≤x =
    f .bwd⊣fwd .proj₂ (X .≤-trans inl fy∨gz≤x) ,
    g .bwd⊣fwd .proj₂ (X .≤-trans inr fy∨gz≤x)
    where open IsJoin (X .joins .∨-isJoin)
  products .pair-cong f₁≈f₂ g₁≈g₂ .fwd-eq = meet-semilattice.⟨⟩-cong (f₁≈f₂ .fwd-eq) (g₁≈g₂ .fwd-eq)
  products .pair-cong f₁≈f₂ g₁≈g₂ .bwd-eq = join-semilattice.[]-cong (f₁≈f₂ .bwd-eq) (g₁≈g₂ .bwd-eq)
  products .pair-p₁ f g .fwd-eq = meet-semilattice.pair-p₁ (f .fwd) (g .fwd)
  products .pair-p₁ f g .bwd-eq = join-semilattice.inj₁-copair (f .bwd) (g .bwd)
  products .pair-p₂ f g .fwd-eq = meet-semilattice.pair-p₂ (f .fwd) (g .fwd)
  products .pair-p₂ f g .bwd-eq = join-semilattice.inj₂-copair (f .bwd) (g .bwd)
  products .pair-ext f .fwd-eq = meet-semilattice.pair-ext (f .fwd)
  products .pair-ext f .bwd-eq = join-semilattice.copair-ext (f .bwd)

-- This category has a lifting monad
module _ where

  𝕃 : Obj → Obj
  𝕃 X .carrier = L (X .carrier)
  𝕃 X .meets = meet-semilattice.L (X .meets)
  𝕃 X .joins = join-semilattice.L (X .joins)

  𝕃-map : ∀ {X Y} → X ⇒g Y → 𝕃 X ⇒g 𝕃 Y
  𝕃-map f .fwd = meet-semilattice.L-map (f .fwd)
  𝕃-map f .bwd = join-semilattice.L-map (f .bwd)
  𝕃-map f .bwd⊣fwd {bottom} {bottom} .proj₁ y≤Lfx = tt
  𝕃-map f .bwd⊣fwd {< x >} {bottom} .proj₁ y≤Lfx = tt
  𝕃-map f .bwd⊣fwd {< x >} {< y >} .proj₁ y≤Lfx = f .bwd⊣fwd .proj₁ y≤Lfx
  𝕃-map f .bwd⊣fwd {bottom} {bottom} .proj₂ Lfy≤x = tt
  𝕃-map f .bwd⊣fwd {< x >} {bottom} .proj₂ Lfy≤x = tt
  𝕃-map f .bwd⊣fwd {< x >} {< y >} .proj₂ Lfy≤x = f .bwd⊣fwd .proj₂ Lfy≤x

  𝕃-unit : ∀ {X} → X ⇒g 𝕃 X
  𝕃-unit .fwd = meet-semilattice.L-unit
  𝕃-unit .bwd = join-semilattice.L-counit
  𝕃-unit {X} .bwd⊣fwd {x} {bottom} .proj₁ tt =
    X .joins .JoinSemilattice.⊥-isBottom .IsBottom.≤-bottom
  𝕃-unit .bwd⊣fwd {x} {< x₁ >} .proj₁ x₁≤x = x₁≤x
  𝕃-unit .bwd⊣fwd {x} {bottom} .proj₂ x₁ = tt
  𝕃-unit .bwd⊣fwd {x} {< x₁ >} .proj₂ x₁≤x = x₁≤x

  𝕃-join : ∀ {X} → 𝕃 (𝕃 X) ⇒g 𝕃 X
  𝕃-join .fwd = meet-semilattice.L-join
  𝕃-join .bwd = join-semilattice.L-dup
  𝕃-join .bwd⊣fwd {bottom} {bottom} .proj₁ e = tt
  𝕃-join .bwd⊣fwd {< bottom >} {bottom} .proj₁ e = tt
  𝕃-join .bwd⊣fwd {< < x > >} {bottom} .proj₁ e = tt
  𝕃-join .bwd⊣fwd {< < x > >} {< x₁ >} .proj₁ e = e
  𝕃-join .bwd⊣fwd {bottom} {bottom} .proj₂ e = tt
  𝕃-join .bwd⊣fwd {< bottom >} {bottom} .proj₂ e = tt
  𝕃-join .bwd⊣fwd {< < x > >} {bottom} .proj₂ e = tt
  𝕃-join .bwd⊣fwd {< < x > >} {< x₁ >} .proj₂ e = e

  𝕃-strength : ∀ {X Y} → (X ⊗ 𝕃 Y) ⇒g 𝕃 (X ⊗ Y)
  𝕃-strength .fwd = meet-semilattice.L-strength
  𝕃-strength .bwd = join-semilattice.L-costrength
  𝕃-strength {X} {Y} .bwd⊣fwd {x , bottom} {bottom} .proj₁ e =
    X .joins .JoinSemilattice.⊥-isBottom .IsBottom.≤-bottom , tt
  𝕃-strength {X} {Y} .bwd⊣fwd {x , < x₁ >} {bottom} .proj₁ e =
    X .joins .JoinSemilattice.⊥-isBottom .IsBottom.≤-bottom , tt
  𝕃-strength {X} {Y} .bwd⊣fwd {x , < x₂ >} {< x₁ >} .proj₁ e = e
  𝕃-strength {X} {Y} .bwd⊣fwd {x , bottom} {bottom} .proj₂ e = tt
  𝕃-strength {X} {Y} .bwd⊣fwd {x , < x₁ >} {bottom} .proj₂ e = tt
  𝕃-strength {X} {Y} .bwd⊣fwd {x , < x₁ >} {< x₂ >} .proj₂ e = e

module _ where

  -- FIXME: split these bits out into other modules, and consider
  -- reusing booleans.

  data presence : Set where
    pr ab : presence

  presence-≤ : presence → presence → Prop
  presence-≤ pr pr = ⊤
  presence-≤ pr ab = ⊥
  presence-≤ ab _ = ⊤

  presence-∧ : presence → presence → presence
  presence-∧ pr y = y
  presence-∧ ab y = ab

  presence-∨ : presence → presence → presence
  presence-∨ pr y = pr
  presence-∨ ab y = y

  open Preorder

  Presence-preorder : Preorder
  Presence-preorder .Carrier = presence
  Presence-preorder ._≤_ = presence-≤
  Presence-preorder .≤-isPreorder .IsPreorder.refl {pr} = tt
  Presence-preorder .≤-isPreorder .IsPreorder.refl {ab} = tt
  Presence-preorder .≤-isPreorder .IsPreorder.trans {pr} {pr} {pr} p q = tt
  Presence-preorder .≤-isPreorder .IsPreorder.trans {ab} {pr} {pr} p q = tt
  Presence-preorder .≤-isPreorder .IsPreorder.trans {ab} {ab} {pr} p q = tt
  Presence-preorder .≤-isPreorder .IsPreorder.trans {ab} {ab} {ab} p q = tt

  Presence : Obj
  Presence .carrier = Presence-preorder
  Presence .meets .MeetSemilattice._∧_ = presence-∧
  Presence .meets .MeetSemilattice.⊤ = pr
  Presence .meets .MeetSemilattice.∧-isMeet .IsMeet.π₁ {pr} {pr} = tt
  Presence .meets .MeetSemilattice.∧-isMeet .IsMeet.π₁ {pr} {ab} = tt
  Presence .meets .MeetSemilattice.∧-isMeet .IsMeet.π₁ {ab} {y} = tt
  Presence .meets .MeetSemilattice.∧-isMeet .IsMeet.π₂ {pr} {pr} = tt
  Presence .meets .MeetSemilattice.∧-isMeet .IsMeet.π₂ {pr} {ab} = tt
  Presence .meets .MeetSemilattice.∧-isMeet .IsMeet.π₂ {ab} {pr} = tt
  Presence .meets .MeetSemilattice.∧-isMeet .IsMeet.π₂ {ab} {ab} = tt
  IsMeet.⟨_,_⟩ (Presence .meets .MeetSemilattice.∧-isMeet) {pr} {pr} {pr} p q = tt
  IsMeet.⟨_,_⟩ (Presence .meets .MeetSemilattice.∧-isMeet) {ab} {pr} {pr} p q = tt
  IsMeet.⟨_,_⟩ (Presence .meets .MeetSemilattice.∧-isMeet) {ab} {pr} {ab} p q = tt
  IsMeet.⟨_,_⟩ (Presence .meets .MeetSemilattice.∧-isMeet) {ab} {ab} {z} p q = tt
  Presence .meets .MeetSemilattice.⊤-isTop .IsTop.≤-top {pr} = tt
  Presence .meets .MeetSemilattice.⊤-isTop .IsTop.≤-top {ab} = tt
  Presence .joins .JoinSemilattice._∨_ = presence-∨
  Presence .joins .JoinSemilattice.⊥ = ab
  Presence .joins .JoinSemilattice.∨-isJoin .IsJoin.inl {pr} {y} = tt
  Presence .joins .JoinSemilattice.∨-isJoin .IsJoin.inl {ab} {pr} = tt
  Presence .joins .JoinSemilattice.∨-isJoin .IsJoin.inl {ab} {ab} = tt
  Presence .joins .JoinSemilattice.∨-isJoin .IsJoin.inr {pr} {pr} = tt
  Presence .joins .JoinSemilattice.∨-isJoin .IsJoin.inr {pr} {ab} = tt
  Presence .joins .JoinSemilattice.∨-isJoin .IsJoin.inr {ab} {pr} = tt
  Presence .joins .JoinSemilattice.∨-isJoin .IsJoin.inr {ab} {ab} = tt
  IsJoin.[_,_] (Presence .joins .JoinSemilattice.∨-isJoin) {pr} {pr} {pr} p q = tt
  IsJoin.[_,_] (Presence .joins .JoinSemilattice.∨-isJoin) {pr} {ab} {pr} p q = tt
  IsJoin.[_,_] (Presence .joins .JoinSemilattice.∨-isJoin) {ab} {pr} {pr} p q = tt
  IsJoin.[_,_] (Presence .joins .JoinSemilattice.∨-isJoin) {ab} {ab} {pr} p q = tt
  IsJoin.[_,_] (Presence .joins .JoinSemilattice.∨-isJoin) {ab} {ab} {ab} p q = tt
  Presence .joins .JoinSemilattice.⊥-isBottom .IsBottom.≤-bottom {pr} = tt
  Presence .joins .JoinSemilattice.⊥-isBottom .IsBottom.≤-bottom {ab} = tt

  -- FIXME: this ought to work for any object, since we can always use
  -- the meets.
  combinePresence : (Presence ⊗ Presence) ⇒g Presence
  combinePresence .fwd ._=>M_.func (x , y) = presence-∧ x y
  combinePresence .fwd ._=>M_.monotone {pr , pr} {pr , pr} (p , q) = tt
  combinePresence .fwd ._=>M_.monotone {pr , ab} {x₂ , y₂} (p , q) = tt
  combinePresence .fwd ._=>M_.monotone {ab , y₁} {x₂ , y₂} (p , q) = tt
  combinePresence .fwd ._=>M_.∧-preserving {pr , pr} {x₂ , y₂} = Presence-preorder .≤-isPreorder .IsPreorder.refl
  combinePresence .fwd ._=>M_.∧-preserving {pr , ab} {x₂ , y₂} = tt
  combinePresence .fwd ._=>M_.∧-preserving {ab , y₁} {x₂ , y₂} = tt
  combinePresence .fwd ._=>M_.⊤-preserving = tt
  combinePresence .bwd ._=>J_.func x = x , x
  combinePresence .bwd ._=>J_.monotone x₁≤x₂ = x₁≤x₂ , x₁≤x₂
  combinePresence .bwd ._=>J_.∨-preserving {pr} {pr} = tt , tt
  combinePresence .bwd ._=>J_.∨-preserving {pr} {ab} = tt , tt
  combinePresence .bwd ._=>J_.∨-preserving {ab} {pr} = tt , tt
  combinePresence .bwd ._=>J_.∨-preserving {ab} {ab} = tt , tt
  combinePresence .bwd ._=>J_.⊥-preserving = tt , tt
  combinePresence .bwd⊣fwd {pr , pr} {y} .proj₁ p = p , p
  combinePresence .bwd⊣fwd {pr , ab} {ab} .proj₁ p = tt , tt
  combinePresence .bwd⊣fwd {ab , pr} {ab} .proj₁ p = tt , tt
  combinePresence .bwd⊣fwd {ab , ab} {ab} .proj₁ p = tt , tt
  combinePresence .bwd⊣fwd {pr , pr} {pr} .proj₂ p = tt
  combinePresence .bwd⊣fwd {pr , pr} {ab} .proj₂ p = tt
  combinePresence .bwd⊣fwd {pr , ab} {ab} .proj₂ p = tt
  combinePresence .bwd⊣fwd {ab , pr} {ab} .proj₂ p = tt
  combinePresence .bwd⊣fwd {ab , ab} {ab} .proj₂ p = tt

  present : 𝟙 ⇒g Presence
  present .fwd ._=>M_.func _ = pr
  present .fwd ._=>M_.monotone _ = tt
  present .fwd ._=>M_.∧-preserving = tt
  present .fwd ._=>M_.⊤-preserving = tt
  present .bwd = join-semilattice.terminal
  present .bwd⊣fwd {_} {pr} = refl-⇔
  present .bwd⊣fwd {_} {ab} = refl-⇔
