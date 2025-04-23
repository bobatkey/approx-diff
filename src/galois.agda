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
open import cmon-enriched

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
-- a reverse derivative.

record Obj : Set (suc 0ℓ) where
  no-eta-equality
  field
    carrier : Preorder
    meets   : MeetSemilattice carrier
    joins   : JoinSemilattice carrier
  open Preorder carrier public
open Obj

record _⇒g_ (X Y : Obj) : Set where
  no-eta-equality
  private
    module X = Obj X
    module Y = Obj Y
  field
    -- FIXME: might be better to call these right and left
    fwd : X .meets =>M Y .meets
    bwd : Y .joins =>J X .joins
    bwd⊣fwd : ∀ {x y} → y Y.≤ (fwd ._=>M_.func x) ⇔ (bwd ._=>J_.func y) X.≤ x

  -- FIXME: preservation of meets and joins comes for free! Make a
  -- helper constructor.
open _⇒g_

record _⇒g'_ (X Y : Obj) : Set where
  no-eta-equality
  open preorder._=>_
  private
    module X = Obj X
    module Y = Obj Y
  field
    right : X .carrier preorder.=> Y .carrier
    left : Y .carrier preorder.=> X .carrier
    left⊣right : ∀ {x y} → y Y.≤ (right .func x) ⇔ (left .func y) X.≤ x

open _⇒g'_

record _≃g_ {X Y : Obj} (f g : X ⇒g Y) : Prop where
  field
    fwd-eq : f .fwd ≃M g .fwd
    bwd-eq : f .bwd ≃J g .bwd
open _≃g_

record _≃g'_ {X Y : Obj} (f g : X ⇒g' Y) : Prop where
  field
    right-eq : f .right ≃m g .right
    left-eq : f .left ≃m g .left
open _≃g'_

open IsEquivalence
open preorder using (≃m-isEquivalence)

≃g-isEquivalence : ∀ {X Y} → IsEquivalence (_≃g_ {X} {Y})
≃g-isEquivalence .refl .fwd-eq = ≃M-isEquivalence .refl
≃g-isEquivalence .refl .bwd-eq = ≃J-isEquivalence .refl
≃g-isEquivalence .sym e .fwd-eq = ≃M-isEquivalence .sym (e .fwd-eq)
≃g-isEquivalence .sym e .bwd-eq = ≃J-isEquivalence .sym (e .bwd-eq)
≃g-isEquivalence .trans e₁ e₂ .fwd-eq = ≃M-isEquivalence .trans (e₁ .fwd-eq) (e₂ .fwd-eq)
≃g-isEquivalence .trans e₁ e₂ .bwd-eq = ≃J-isEquivalence .trans (e₁ .bwd-eq) (e₂ .bwd-eq)

≃g'-isEquivalence : ∀ {X Y} → IsEquivalence (_≃g'_ {X} {Y})
≃g'-isEquivalence .refl .right-eq = ≃m-isEquivalence .refl
≃g'-isEquivalence .refl .left-eq = ≃m-isEquivalence .refl
≃g'-isEquivalence .sym e .right-eq = ≃m-isEquivalence .sym (e .right-eq)
≃g'-isEquivalence .sym e .left-eq = ≃m-isEquivalence .sym (e .left-eq)
≃g'-isEquivalence .trans e₁ e₂ .right-eq = ≃m-isEquivalence .trans (e₁ .right-eq) (e₂ .right-eq)
≃g'-isEquivalence .trans e₁ e₂ .left-eq = ≃m-isEquivalence .trans (e₁ .left-eq) (e₂ .left-eq)

idg : (X : Obj) → X ⇒g X
idg X .fwd = idM
idg X .bwd = idJ
idg X .bwd⊣fwd = refl-⇔

idg' : (X : Obj) → X ⇒g' X
idg' X .right = id
idg' X .left = id
idg' X .left⊣right = refl-⇔

_∘g_ : ∀ {X Y Z : Obj} → Y ⇒g Z → X ⇒g Y → X ⇒g Z
(f ∘g g) .fwd = f .fwd ∘M g .fwd
(f ∘g g) .bwd = g .bwd ∘J f .bwd
(f ∘g g) .bwd⊣fwd = trans-⇔ (f .bwd⊣fwd) (g .bwd⊣fwd)

_∘g'_ : ∀ {X Y Z : Obj} → Y ⇒g' Z → X ⇒g' Y → X ⇒g' Z
(f ∘g' g) .right = f .right ∘ g .right
(f ∘g' g) .left = g .left ∘ f .left
(f ∘g' g) .left⊣right = trans-⇔ (f .left⊣right) (g .left⊣right)

∘g-cong : ∀ {X Y Z}{f₁ f₂ : Y ⇒g Z}{g₁ g₂ : X ⇒g Y} → f₁ ≃g f₂ → g₁ ≃g g₂ → (f₁ ∘g g₁) ≃g (f₂ ∘g g₂)
∘g-cong f₁≈f₂ g₁≈g₂ .fwd-eq = meet-semilattice.∘-cong (f₁≈f₂ .fwd-eq) (g₁≈g₂ .fwd-eq)
∘g-cong f₁≈f₂ g₁≈g₂ .bwd-eq = join-semilattice.∘-cong (g₁≈g₂ .bwd-eq) (f₁≈f₂ .bwd-eq)

∘g'-cong : ∀ {X Y Z}{f₁ f₂ : Y ⇒g' Z}{g₁ g₂ : X ⇒g' Y} → f₁ ≃g' f₂ → g₁ ≃g' g₂ → (f₁ ∘g' g₁) ≃g' (f₂ ∘g' g₂)
∘g'-cong f₁≈f₂ g₁≈g₂ .right-eq = ∘-cong (f₁≈f₂ .right-eq) (g₁≈g₂ .right-eq)
∘g'-cong f₁≈f₂ g₁≈g₂ .left-eq = ∘-cong (g₁≈g₂ .left-eq) (f₁≈f₂ .left-eq)

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat .Category.obj = Obj
cat .Category._⇒_ = _⇒g_
cat .Category._≈_ = _≃g_
cat .Category.isEquiv = ≃g-isEquivalence
cat .Category.id = idg
cat .Category._∘_ = _∘g_
cat .Category.∘-cong = ∘g-cong
cat .Category.id-left .fwd-eq = meet-semilattice.id-left
cat .Category.id-left .bwd-eq = join-semilattice.id-right
cat .Category.id-right .fwd-eq = meet-semilattice.id-right
cat .Category.id-right .bwd-eq = join-semilattice.id-left
cat .Category.assoc f g h .fwd-eq = meet-semilattice.assoc (f .fwd) (g .fwd) (h .fwd)
cat .Category.assoc f g h .bwd-eq =
  ≃J-isEquivalence .sym (join-semilattice.assoc (h .bwd) (g .bwd) (f .bwd))

cat' : Category (suc 0ℓ) 0ℓ 0ℓ
cat' .Category.obj = Obj
cat' .Category._⇒_ = _⇒g'_
cat' .Category._≈_ = _≃g'_
cat' .Category.isEquiv = ≃g'-isEquivalence
cat' .Category.id = idg'
cat' .Category._∘_ = _∘g'_
cat' .Category.∘-cong = ∘g'-cong
cat' .Category.id-left .right-eq = id-left
cat' .Category.id-left .left-eq = id-right
cat' .Category.id-right .right-eq = id-right
cat' .Category.id-right .left-eq = id-left
cat' .Category.assoc f g h .right-eq = assoc (f .right) (g .right) (h .right)
cat' .Category.assoc f g h .left-eq =
  ≃m-isEquivalence .sym (assoc (h .left) (g .left) (f .left))

------------------------------------------------------------------------------
-- CMon enrichment
module _ {X Y : Obj} where
  open preorder._=>_

  private
    module YM = MeetSemilattice (Y .meets)
    module XJ = JoinSemilattice (X .joins)

  εm : X ⇒g Y
  εm .fwd = meet-semilattice.εm
  εm .bwd = join-semilattice.εm
  εm .bwd⊣fwd .proj₁ _ = XJ.≤-bottom
  εm .bwd⊣fwd .proj₂ _ = YM.≤-top

  εm' : X ⇒g' Y
  εm' .right .func x = YM.⊤
  εm' .right .mono _ = Y .≤-refl
  εm' .left .func x = XJ.⊥
  εm' .left .mono x = X .≤-refl
  εm' .left⊣right .proj₁ _ = XJ.≤-bottom
  εm' .left⊣right .proj₂ _ = YM.≤-top

  _+m_ : X ⇒g Y → X ⇒g Y → X ⇒g Y
  (f +m g) .fwd = meet-semilattice._+m_ (f .fwd) (g .fwd)
  (f +m g) .bwd = join-semilattice._+m_ (f .bwd) (g .bwd)
  (f +m g) .bwd⊣fwd {x} {y} .proj₁ y≤fx∧gx =
    XJ.[ f .bwd⊣fwd .proj₁ (Y .≤-trans y≤fx∧gx YM.π₁)
       ∨ g .bwd⊣fwd .proj₁ (Y .≤-trans y≤fx∧gx YM.π₂)
       ]
  (f +m g) .bwd⊣fwd {x} {y} .proj₂ fy∨gy≤x =
    YM.⟨ f .bwd⊣fwd .proj₂ (X .≤-trans XJ.inl fy∨gy≤x)
       ∧ g .bwd⊣fwd .proj₂ (X .≤-trans XJ.inr fy∨gy≤x)
       ⟩

  _+m'_ : X ⇒g' Y → X ⇒g' Y → X ⇒g' Y
  (f +m' g) .right .func x = {!   !}
  (f +m' g) .right .mono _ = {!   !}
  (f +m' g) .left = {!   !}
  (f +m' g) .left⊣right {x} {y} .proj₁ y≤fx∧gx = {!   !}

  +m-cong : ∀ {f₁ f₂ g₁ g₂ : X ⇒g Y} → f₁ ≃g f₂ → g₁ ≃g g₂ → (f₁ +m g₁) ≃g (f₂ +m g₂)
  +m-cong f₁≃f₂ g₁≃g₂ .fwd-eq = meet-semilattice.+m-cong (f₁≃f₂ .fwd-eq) (g₁≃g₂ .fwd-eq)
  +m-cong f₁≃f₂ g₁≃g₂ .bwd-eq = join-semilattice.+m-cong (f₁≃f₂ .bwd-eq) (g₁≃g₂ .bwd-eq)

  +m-comm : ∀ {f g} → (f +m g) ≃g (g +m f)
  +m-comm {f} {g} .fwd-eq = meet-semilattice.+m-comm {f = f .fwd} {g = g .fwd}
  +m-comm {f} {g} .bwd-eq = join-semilattice.+m-comm {f = f .bwd} {g = g .bwd}

  +m-assoc : ∀ {f g h} → ((f +m g) +m h) ≃g (f +m (g +m h))
  +m-assoc {f} {g} {h} .fwd-eq = meet-semilattice.+m-assoc {f = f .fwd} {g .fwd} {h .fwd}
  +m-assoc {f} {g} {h} .bwd-eq = join-semilattice.+m-assoc {f = f .bwd} {g .bwd} {h .bwd}

  +m-lunit : ∀ {f} → (εm +m f) ≃g f
  +m-lunit {f} .fwd-eq = meet-semilattice.+m-lunit {f = f .fwd}
  +m-lunit {f} .bwd-eq = join-semilattice.+m-lunit {f = f .bwd}

module _ where

  open import commutative-monoid

  open CommutativeMonoid

  cmon-enriched : CMonEnriched cat
  cmon-enriched .CMonEnriched.homCM X Y .ε = εm
  cmon-enriched .CMonEnriched.homCM X Y ._+_ = _+m_
  cmon-enriched .CMonEnriched.homCM X Y .+-cong = +m-cong
  cmon-enriched .CMonEnriched.homCM X Y .+-lunit = +m-lunit
  cmon-enriched .CMonEnriched.homCM X Y .+-assoc = +m-assoc
  cmon-enriched .CMonEnriched.homCM X Y .+-comm = +m-comm
  cmon-enriched .CMonEnriched.comp-bilinear₁ f₁ f₂ g .fwd-eq =
    meet-semilattice.comp-bilinear₁ (f₁ .fwd) (f₂ .fwd) (g .fwd)
  cmon-enriched .CMonEnriched.comp-bilinear₁ f₁ f₂ g .bwd-eq =
    join-semilattice.comp-bilinear₂ (g .bwd) (f₁ .bwd) (f₂ .bwd)
  cmon-enriched .CMonEnriched.comp-bilinear₂ f g₁ g₂ .fwd-eq =
    meet-semilattice.comp-bilinear₂ (f .fwd) (g₁ .fwd) (g₂ .fwd)
  cmon-enriched .CMonEnriched.comp-bilinear₂ f g₁ g₂ .bwd-eq =
    join-semilattice.comp-bilinear₁ (g₁ .bwd) (g₂ .bwd) (f .bwd)
  cmon-enriched .CMonEnriched.comp-bilinear-ε₁ f .fwd-eq =
    meet-semilattice.comp-bilinear-ε₁ (f .fwd)
  cmon-enriched .CMonEnriched.comp-bilinear-ε₁ f .bwd-eq =
    join-semilattice.comp-bilinear-ε₂ (f .bwd)
  cmon-enriched .CMonEnriched.comp-bilinear-ε₂ f .fwd-eq =
    meet-semilattice.comp-bilinear-ε₂ (f .fwd)
  cmon-enriched .CMonEnriched.comp-bilinear-ε₂ f .bwd-eq =
    join-semilattice.comp-bilinear-ε₁ (f .bwd)

------------------------------------------------------------------------------
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

  -- FIXME: this is misnamed: should be _⊕_
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
  products .p₁ {X} {Y} .bwd⊣fwd {x , y} {x'} .proj₁ x'≤x .proj₂ = Y.≤-bottom
    where module Y = JoinSemilattice (Y .joins)
  products .p₁ {X} {Y} .bwd⊣fwd {x , y} {x'} .proj₂ = proj₁
  products .p₂ .fwd = meet-semilattice.project₂
  products .p₂ .bwd = join-semilattice.inject₂
  products .p₂ {X} {Y} .bwd⊣fwd {x , y} {y'} .proj₁ y'≤y .proj₁ = X.≤-bottom
    where module X = JoinSemilattice (X .joins)
  products .p₂ {X} {Y} .bwd⊣fwd {x , y} {y'} .proj₁ y'≤y .proj₂ = y'≤y
  products .p₂ {X} {Y} .bwd⊣fwd {x , y} {y'} .proj₂ = proj₂
  products .pair f g .fwd = meet-semilattice.⟨ f .fwd , g .fwd ⟩
  products .pair f g .bwd = join-semilattice.[ f .bwd , g .bwd ]
  products .pair {X} {Y} {Z} f g .bwd⊣fwd {x} {y , z} .proj₁ (y≤fx , z≤gx) =
    [ f .bwd⊣fwd .proj₁ y≤fx , g .bwd⊣fwd .proj₁ z≤gx ]
    where open IsJoin (X .joins .∨-isJoin)
  products .pair {X} {Y} {Z} f g .bwd⊣fwd {x} {y , z} .proj₂ fy∨gz≤x =
    f .bwd⊣fwd .proj₂ (X .≤-trans X.inl fy∨gz≤x) ,
    g .bwd⊣fwd .proj₂ (X .≤-trans X.inr fy∨gz≤x)
    where module X = JoinSemilattice (X .joins)
  products .pair-cong f₁≈f₂ g₁≈g₂ .fwd-eq = meet-semilattice.⟨⟩-cong (f₁≈f₂ .fwd-eq) (g₁≈g₂ .fwd-eq)
  products .pair-cong f₁≈f₂ g₁≈g₂ .bwd-eq = join-semilattice.[]-cong (f₁≈f₂ .bwd-eq) (g₁≈g₂ .bwd-eq)
  products .pair-p₁ f g .fwd-eq = meet-semilattice.pair-p₁ (f .fwd) (g .fwd)
  products .pair-p₁ f g .bwd-eq = join-semilattice.inj₁-copair (f .bwd) (g .bwd)
  products .pair-p₂ f g .fwd-eq = meet-semilattice.pair-p₂ (f .fwd) (g .fwd)
  products .pair-p₂ f g .bwd-eq = join-semilattice.inj₂-copair (f .bwd) (g .bwd)
  products .pair-ext f .fwd-eq = meet-semilattice.pair-ext (f .fwd)
  products .pair-ext f .bwd-eq = join-semilattice.copair-ext (f .bwd)

{-
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
-}

module _ where

  open import two using (Two; I; O)

  TWO : Obj
  TWO .carrier .Preorder.Carrier = Two
  TWO .carrier .Preorder._≤_ = two._≤_
  TWO .carrier .Preorder.≤-isPreorder = two.≤-isPreorder
  TWO .meets .MeetSemilattice._∧_ = two._⊓_
  TWO .meets .MeetSemilattice.⊤ = I
  TWO .meets .MeetSemilattice.∧-isMeet = two.⊓-isMeet
  TWO .meets .MeetSemilattice.⊤-isTop .IsTop.≤-top = two.I-top
  TWO .joins .JoinSemilattice._∨_ = two._⊔_
  TWO .joins .JoinSemilattice.⊥ = O
  TWO .joins .JoinSemilattice.∨-isJoin = two.⊔-isJoin
  TWO .joins .JoinSemilattice.⊥-isBottom .IsBottom.≤-bottom {x} = two.O-bot {x}

  open HasProducts products

  -- This is a monoid because every object in this category is a
  -- monoid by cmon-enrichment. FIXME: actually prove this gives a
  -- monoid.

  conjunct : (TWO ⊗ TWO) ⇒g TWO
  conjunct = p₁ +m p₂

  unit : 𝟙 ⇒g TWO
  unit = εm
