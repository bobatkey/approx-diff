{-# OPTIONS --postfix-projections --prop --safe #-}

module galois where

open import Level hiding (_⊔_)
open import Data.Product using (_,_; proj₁; proj₂)
open import prop hiding (_∨_; ⊥; _∧_)
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
  open MeetSemilattice meets renaming (idem to ∧-idem; interchange to ∧-interchange) public
  open JoinSemilattice joins renaming (idem to ∨-idem; interchange to ∨-interchange) public
open Obj

record _⇒g_ (X Y : Obj) : Set where
  no-eta-equality
  open _=>M_
  open _=>J_
  open preorder._=>_

  private
    module X = Obj X
    module Y = Obj Y
    module XM = MeetSemilattice (X .meets)
    module YM = MeetSemilattice (Y .meets)
    module XJ = JoinSemilattice (X .joins)
    module YJ = JoinSemilattice (Y .joins)
  field
    -- could define this structure just for preorders (with a bit more indirection)
    right : X .carrier preorder.=> Y .carrier
    left : Y .carrier preorder.=> X .carrier
    left⊣right : ∀ {x y} → y Y.≤ (right .fun x) ⇔ (left .fun y) X.≤ x

  -- right adjoint preserves meets
  right-∧ : X .meets =>M Y .meets
  right-∧ .func = right
  right-∧ .∧-preserving = left⊣right .proj₂ XM.⟨ left⊣right .proj₁ YM.π₁ ∧ left⊣right .proj₁ YM.π₂ ⟩
  right-∧ .⊤-preserving = left⊣right .proj₂ XM.≤-top

  -- left adjoint preserves joins
  left-∨ : Y .joins =>J X .joins
  left-∨ .func = left
  left-∨ .∨-preserving = left⊣right .proj₁ YJ.[ left⊣right .proj₂ XJ.inl ∨ left⊣right .proj₂ XJ.inr ]
  left-∨ .⊥-preserving = left⊣right .proj₁ YJ.≤-bottom

open _⇒g_

record _≃g_ {X Y : Obj} (f g : X ⇒g Y) : Prop where
  field
    right-eq : f .right ≃m g .right
    left-eq : f .left ≃m g .left

  left-∨-cong : left-∨ f ≃J left-∨ g
  left-∨-cong ._≃J_.eqfunc = left-eq

  right-∧-cong : right-∧ f ≃M right-∧ g
  right-∧-cong ._≃M_.eqfunc = right-eq

open _≃g_

open IsEquivalence
open preorder using (≃m-isEquivalence)

≃g-isEquivalence : ∀ {X Y} → IsEquivalence (_≃g_ {X} {Y})
≃g-isEquivalence .refl .right-eq = ≃m-isEquivalence .refl
≃g-isEquivalence .refl .left-eq = ≃m-isEquivalence .refl
≃g-isEquivalence .sym e .right-eq = ≃m-isEquivalence .sym (e .right-eq)
≃g-isEquivalence .sym e .left-eq = ≃m-isEquivalence .sym (e .left-eq)
≃g-isEquivalence .trans e₁ e₂ .right-eq = ≃m-isEquivalence .trans (e₁ .right-eq) (e₂ .right-eq)
≃g-isEquivalence .trans e₁ e₂ .left-eq = ≃m-isEquivalence .trans (e₁ .left-eq) (e₂ .left-eq)

idg : (X : Obj) → X ⇒g X
idg X .right = id
idg X .left = id
idg X .left⊣right = refl-⇔

_∘g_ : ∀ {X Y Z : Obj} → Y ⇒g Z → X ⇒g Y → X ⇒g Z
(f ∘g g) .right = f .right ∘ g .right
(f ∘g g) .left = g .left ∘ f .left
(f ∘g g) .left⊣right = trans-⇔ (f .left⊣right) (g .left⊣right)

∘g-cong : ∀ {X Y Z}{f₁ f₂ : Y ⇒g Z}{g₁ g₂ : X ⇒g Y} → f₁ ≃g f₂ → g₁ ≃g g₂ → (f₁ ∘g g₁) ≃g (f₂ ∘g g₂)
∘g-cong f₁≈f₂ g₁≈g₂ .right-eq = ∘-cong (f₁≈f₂ .right-eq) (g₁≈g₂ .right-eq)
∘g-cong f₁≈f₂ g₁≈g₂ .left-eq = ∘-cong (g₁≈g₂ .left-eq) (f₁≈f₂ .left-eq)

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat .Category.obj = Obj
cat .Category._⇒_ = _⇒g_
cat .Category._≈_ = _≃g_
cat .Category.isEquiv = ≃g-isEquivalence
cat .Category.id = idg
cat .Category._∘_ = _∘g_
cat .Category.∘-cong = ∘g-cong
cat .Category.id-left .right-eq = id-left
cat .Category.id-left .left-eq = id-right
cat .Category.id-right .right-eq = id-right
cat .Category.id-right .left-eq = id-left
cat .Category.assoc f g h .right-eq = assoc (f .right) (g .right) (h .right)
cat .Category.assoc f g h .left-eq =
  ≃m-isEquivalence .sym (assoc (h .left) (g .left) (f .left))

------------------------------------------------------------------------------
-- CMon enrichment
module _ {X Y : Obj} where
  open _=>_
  open preorder._=>_
  open preorder._≃m_

  private
    module YM = MeetSemilattice (Y .meets)
    module XJ = JoinSemilattice (X .joins)

  εm : X ⇒g Y
  εm .right = meet-semilattice.εm {X = X .meets} {Y = Y .meets} ._=>M_.func
  εm .left = join-semilattice.εm {X = Y .joins} {Y = X .joins} ._=>J_.func
  εm .left⊣right .proj₁ _ = XJ.≤-bottom
  εm .left⊣right .proj₂ _ = YM.≤-top

  _+m_ : X ⇒g Y → X ⇒g Y → X ⇒g Y
  (f +m g) .right = meet-semilattice._+m_ (right-∧ f) (right-∧ g) ._=>M_.func
  (f +m g) .left = join-semilattice._+m_ (left-∨ f) (left-∨ g) ._=>J_.func
  (f +m g) .left⊣right {x} {y} .proj₁ y≤fx∧gx =
    XJ.[ f .left⊣right .proj₁ (Y .≤-trans y≤fx∧gx YM.π₁)
       ∨ g .left⊣right .proj₁ (Y .≤-trans y≤fx∧gx YM.π₂)
       ]
  (f +m g) .left⊣right {x} {y} .proj₂ fy∨gy≤x =
    YM.⟨ f .left⊣right .proj₂ (X .≤-trans XJ.inl fy∨gy≤x)
       ∧ g .left⊣right .proj₂ (X .≤-trans XJ.inr fy∨gy≤x)
       ⟩

  +m-cong : ∀ {f₁ f₂ g₁ g₂ : X ⇒g Y} → f₁ ≃g f₂ → g₁ ≃g g₂ → (f₁ +m g₁) ≃g (f₂ +m g₂)
  +m-cong f₁≃f₂ g₁≃g₂ .right-eq = meet-semilattice.+m-cong (right-∧-cong f₁≃f₂) (right-∧-cong g₁≃g₂) ._≃M_.eqfunc
  +m-cong f₁≃f₂ g₁≃g₂ .left-eq = join-semilattice.+m-cong (left-∨-cong f₁≃f₂) (left-∨-cong g₁≃g₂) ._≃J_.eqfunc

  -- Could give more directly rather than factoring through meet-/join-semilattices
  +m-comm : ∀ {f g} → (f +m g) ≃g (g +m f)
  +m-comm {f} {g} .right-eq = meet-semilattice.+m-comm {f = right-∧ f} {right-∧ g} ._≃M_.eqfunc
  +m-comm {f} {g} .left-eq = join-semilattice.+m-comm {f = left-∨ f} {left-∨ g} ._≃J_.eqfunc

  +m-assoc : ∀ {f g h} → ((f +m g) +m h) ≃g (f +m (g +m h))
  +m-assoc {f} {g} {h} .right-eq = meet-semilattice.+m-assoc {f = right-∧ f} {right-∧ g} {right-∧ h} ._≃M_.eqfunc
  +m-assoc {f} {g} {h} .left-eq = join-semilattice.+m-assoc {f = left-∨ f} {left-∨ g} {left-∨ h} ._≃J_.eqfunc

  +m-lunit : ∀ {f} → (εm +m f) ≃g f
  +m-lunit {f} .right-eq = meet-semilattice.+m-lunit {f = right-∧ f} ._≃M_.eqfunc
  +m-lunit {f} .left-eq = join-semilattice.+m-lunit {f = left-∨ f} ._≃J_.eqfunc

module _ where
  open import commutative-monoid
  open CommutativeMonoid
  open _=>_
  open preorder._≃m_

  cmon-enriched : CMonEnriched cat
  cmon-enriched .CMonEnriched.homCM X Y .ε = εm
  cmon-enriched .CMonEnriched.homCM X Y ._+_ = _+m_
  cmon-enriched .CMonEnriched.homCM X Y .+-cong = +m-cong
  cmon-enriched .CMonEnriched.homCM X Y .+-lunit = +m-lunit
  cmon-enriched .CMonEnriched.homCM X Y .+-assoc = +m-assoc
  cmon-enriched .CMonEnriched.homCM X Y .+-comm = +m-comm
  cmon-enriched .CMonEnriched.comp-bilinear₁ {Z = Z} f₁ f₂ g .right-eq .eqfun x = Z .≃-refl
  cmon-enriched .CMonEnriched.comp-bilinear₁ f₁ f₂ g .left-eq .eqfun x =
    _=>J_.∨-preserving-≃ (left-∨ g)
  cmon-enriched .CMonEnriched.comp-bilinear₂ {Z = Z} f g₁ g₂ .right-eq .eqfun x =
    Z .≃-sym (_=>M_.∧-preserving-≃ (right-∧ f))
  cmon-enriched .CMonEnriched.comp-bilinear₂ {X = X} f g₁ g₂ .left-eq .eqfun x = X .≃-refl
  cmon-enriched .CMonEnriched.comp-bilinear-ε₁ {Z = Z} f .right-eq .eqfun x = Z .≃-refl
  cmon-enriched .CMonEnriched.comp-bilinear-ε₁ f .left-eq .eqfun x =
    _=>J_.⊥-preserving-≃ (left-∨ f)
  cmon-enriched .CMonEnriched.comp-bilinear-ε₂ {Z = Z} f .right-eq .eqfun x =
    Z .≃-sym (_=>M_.⊤-preserving-≃ (right-∧ f))
  cmon-enriched .CMonEnriched.comp-bilinear-ε₂ {X = X} f .left-eq .eqfun x = X .≃-refl

------------------------------------------------------------------------------
-- Terminal (FIXME: and initial)
module _ where
  open IsTerminal
  open HasTerminal

  𝟙 : Obj
  𝟙 .carrier = preorder.𝟙
  𝟙 .meets = meet-semilattice.𝟙
  𝟙 .joins = join-semilattice.𝟙

  to-𝟙 : ∀ X → X ⇒g 𝟙
  to-𝟙 X .right = meet-semilattice.terminal {X = X .meets} ._=>M_.func
  to-𝟙 X .left = join-semilattice.initial {X = X .joins} ._=>J_.func
  to-𝟙 X .left⊣right .proj₁ tt =
    X .joins .JoinSemilattice.⊥-isBottom .IsBottom.≤-bottom
  to-𝟙 X .left⊣right .proj₂ _ = tt

  terminal : HasTerminal cat
  terminal .witness = 𝟙
  terminal .is-terminal .to-terminal = to-𝟙 _
  terminal .is-terminal .to-terminal-ext {X} f .right-eq =
    meet-semilattice.terminal-unique (X .meets) (right-∧ f) _ ._≃M_.eqfunc
  terminal .is-terminal .to-terminal-ext {X} f .left-eq =
    join-semilattice.initial-unique (X .joins) (left-∨ (to-𝟙 X)) (left-∨ f) ._≃J_.eqfunc

-- This category has binary products (FIXME: and biproducts)
module _ where

  open HasProducts

  _⊕_ : Obj → Obj → Obj
  (X ⊕ Y) .carrier = X .carrier × Y .carrier
  (X ⊕ Y) .meets = X .meets ⊕M Y .meets
  (X ⊕ Y) .joins = X .joins ⊕J Y .joins

  open import Data.Product using (proj₁; proj₂; _,_)
  open JoinSemilattice
  open MeetSemilattice
  open _=>_
  open preorder._≃m_

  products : HasProducts cat
  products .prod = _⊕_
  products .p₁ {X} {Y} .right = meet-semilattice.project₁ {X = X .meets} {Y = Y .meets} ._=>M_.func
  products .p₁ {X} {Y} .left = join-semilattice.inject₁ {X = X .joins} {Y = Y .joins} ._=>J_.func
  products .p₁ .left⊣right {x , y} {x'} .proj₁ x'≤x .proj₁ = x'≤x
  products .p₁ {X} {Y} .left⊣right {x , y} {x'} .proj₁ x'≤x .proj₂ = Y.≤-bottom
    where module Y = JoinSemilattice (Y .joins)
  products .p₁ .left⊣right {x , y} {x'} .proj₂ = proj₁
  products .p₂ {X} {Y} .right = meet-semilattice.project₂ {X = X .meets} {Y = Y .meets} ._=>M_.func
  products .p₂ {X} {Y} .left = join-semilattice.inject₂ {X = X .joins} {Y = Y .joins} ._=>J_.func
  products .p₂ {X} {Y} .left⊣right {x , y} {y'} .proj₁ y'≤y .proj₁ = X.≤-bottom
    where module X = JoinSemilattice (X .joins)
  products .p₂ .left⊣right {x , y} {y'} .proj₁ y'≤y .proj₂ = y'≤y
  products .p₂ .left⊣right {x , y} {y'} .proj₂ = proj₂
  products .pair f g .right = meet-semilattice.⟨ right-∧ f , right-∧ g ⟩ ._=>M_.func
  products .pair f g .left = join-semilattice.[ left-∨ f , left-∨ g ] ._=>J_.func
  products .pair {X} {Y} {Z} f g .left⊣right {x} {y , z} .proj₁ (y≤fx , z≤gx) =
    [ f .left⊣right .proj₁ y≤fx , g .left⊣right .proj₁ z≤gx ]
    where open IsJoin (X .joins .∨-isJoin)
  products .pair {X} {Y} {Z} f g .left⊣right {x} {y , z} .proj₂ fy∨gz≤x =
    f .left⊣right .proj₂ (X .≤-trans X.inl fy∨gz≤x) ,
    g .left⊣right .proj₂ (X .≤-trans X.inr fy∨gz≤x)
    where module X = JoinSemilattice (X .joins)
  products .pair-cong f₁≈f₂ g₁≈g₂ .right-eq =
    meet-semilattice.⟨⟩-cong (right-∧-cong f₁≈f₂) (right-∧-cong g₁≈g₂) ._≃M_.eqfunc
  products .pair-cong f₁≈f₂ g₁≈g₂ .left-eq =
    join-semilattice.[]-cong (left-∨-cong f₁≈f₂) (left-∨-cong g₁≈g₂) ._≃J_.eqfunc
  products .pair-p₁ f g .right-eq = meet-semilattice.pair-p₁ (right-∧ f) (right-∧ g) ._≃M_.eqfunc
  products .pair-p₁ f g .left-eq = join-semilattice.inj₁-copair (left-∨ f) (left-∨ g) ._≃J_.eqfunc
  products .pair-p₂ f g .right-eq = meet-semilattice.pair-p₂ (right-∧ f) (right-∧ g) ._≃M_.eqfunc
  products .pair-p₂ f g .left-eq = join-semilattice.inj₂-copair (left-∨ f) (left-∨ g) ._≃J_.eqfunc
  products .pair-ext f .right-eq = meet-semilattice.pair-ext (right-∧ f) ._≃M_.eqfunc
  products .pair-ext f .left-eq = join-semilattice.copair-ext (left-∨ f) ._≃J_.eqfunc

-- This category has a lifting monad
module _ where

  𝕃 : Obj → Obj
  𝕃 X .carrier = L (X .carrier)
  𝕃 X .meets = meet-semilattice.L (X .meets)
  𝕃 X .joins = join-semilattice.L (X .joins)

  𝕃-map : ∀ {X Y} → X ⇒g Y → 𝕃 X ⇒g 𝕃 Y
  𝕃-map f .right = meet-semilattice.L-map (right-∧ f) ._=>M_.func
  𝕃-map f .left = join-semilattice.L-map (left-∨ f) ._=>J_.func
  𝕃-map f .left⊣right {bottom} {bottom} .proj₁ y≤Lfx = tt
  𝕃-map f .left⊣right {< x >} {bottom} .proj₁ y≤Lfx = tt
  𝕃-map f .left⊣right {< x >} {< y >} .proj₁ y≤Lfx = f .left⊣right .proj₁ y≤Lfx
  𝕃-map f .left⊣right {bottom} {bottom} .proj₂ Lfy≤x = tt
  𝕃-map f .left⊣right {< x >} {bottom} .proj₂ Lfy≤x = tt
  𝕃-map f .left⊣right {< x >} {< y >} .proj₂ Lfy≤x = f .left⊣right .proj₂ Lfy≤x

  𝕃-unit : ∀ {X} → X ⇒g 𝕃 X
  𝕃-unit {X} .right = meet-semilattice.L-unit {X = X .meets} ._=>M_.func
  𝕃-unit {X} .left = join-semilattice.L-counit {X = X .joins} ._=>J_.func
  𝕃-unit {X} .left⊣right {x} {bottom} .proj₁ tt =
    X .joins .JoinSemilattice.⊥-isBottom .IsBottom.≤-bottom
  𝕃-unit .left⊣right {x} {< x₁ >} .proj₁ x₁≤x = x₁≤x
  𝕃-unit .left⊣right {x} {bottom} .proj₂ x₁ = tt
  𝕃-unit .left⊣right {x} {< x₁ >} .proj₂ x₁≤x = x₁≤x

  𝕃-join : ∀ {X} → 𝕃 (𝕃 X) ⇒g 𝕃 X
  𝕃-join {X} .right = meet-semilattice.L-join {X = X .meets} ._=>M_.func
  𝕃-join {X} .left = join-semilattice.L-dup {X = X .joins} ._=>J_.func
  𝕃-join .left⊣right {bottom} {bottom} .proj₁ e = tt
  𝕃-join .left⊣right {< bottom >} {bottom} .proj₁ e = tt
  𝕃-join .left⊣right {< < x > >} {bottom} .proj₁ e = tt
  𝕃-join .left⊣right {< < x > >} {< x₁ >} .proj₁ e = e
  𝕃-join .left⊣right {bottom} {bottom} .proj₂ e = tt
  𝕃-join .left⊣right {< bottom >} {bottom} .proj₂ e = tt
  𝕃-join .left⊣right {< < x > >} {bottom} .proj₂ e = tt
  𝕃-join .left⊣right {< < x > >} {< x₁ >} .proj₂ e = e

  𝕃-strength : ∀ {X Y} → (X ⊕ 𝕃 Y) ⇒g 𝕃 (X ⊕ Y)
  𝕃-strength {X} {Y} .right = meet-semilattice.L-strength {X = X .meets} {Y .meets} ._=>M_.func
  𝕃-strength {X} {Y} .left = join-semilattice.L-costrength {X = X .joins} {Y .joins} ._=>J_.func
  𝕃-strength {X} .left⊣right {x , bottom} {bottom} .proj₁ e =
    X .joins .JoinSemilattice.⊥-isBottom .IsBottom.≤-bottom , tt
  𝕃-strength {X} .left⊣right {x , < x₁ >} {bottom} .proj₁ e =
    X .joins .JoinSemilattice.⊥-isBottom .IsBottom.≤-bottom , tt
  𝕃-strength .left⊣right {x , < x₂ >} {< x₁ >} .proj₁ e = e
  𝕃-strength .left⊣right {x , bottom} {bottom} .proj₂ e = tt
  𝕃-strength .left⊣right {x , < x₁ >} {bottom} .proj₂ e = tt
  𝕃-strength .left⊣right {x , < x₁ >} {< x₂ >} .proj₂ e = e

module _ where

  open import two using (Two; I; O; _⊓_; _⊔_)

  TWO : Obj
  TWO .carrier .Preorder.Carrier = Two
  TWO .carrier .Preorder._≤_ = two._≤_
  TWO .carrier .Preorder.≤-isPreorder = two.≤-isPreorder
  TWO .meets .MeetSemilattice._∧_ = _⊓_
  TWO .meets .MeetSemilattice.⊤ = I
  TWO .meets .MeetSemilattice.∧-isMeet = two.⊓-isMeet
  TWO .meets .MeetSemilattice.⊤-isTop = two.I-isTop
  TWO .joins .JoinSemilattice._∨_ = _⊔_
  TWO .joins .JoinSemilattice.⊥ = O
  TWO .joins .JoinSemilattice.∨-isJoin = two.⊔-isJoin
  TWO .joins .JoinSemilattice.⊥-isBottom = two.O-isBottom

  -- This is a monoid because every object in this category is a
  -- monoid by cmon-enrichment. FIXME: actually prove this gives a
  -- monoid.
  open HasProducts products

  conjunct : (TWO ⊕ TWO) ⇒g TWO
  conjunct = p₁ +m p₂

  unit : 𝟙 ⇒g TWO
  unit = εm

module _ where
  open import two using (Two; I; O; _⊓_; _⊔_)

  open import prop using (_⇔_)

  -- For a fixed y ∈ Two, (- ⊓ y) ⊣ (¬y ⊔ -) is a Galois connection Two → Two.
  -- FIXME: add a notation for Boolean implication?
  ⊓y⊣y→ : ∀ {x y z : Two} → two._≤_ (x ⊓ y) z ⇔ two._≤_ x (two.¬ y ⊔ z)
  ⊓y⊣y→ {O} {_} {_} .proj₁ _ = tt
  ⊓y⊣y→ {I} {O} {_} .proj₁ _ = tt
  ⊓y⊣y→ {I} {I} {O} .proj₁ ()
  ⊓y⊣y→ {I} {I} {I} .proj₁ _ = tt
  ⊓y⊣y→ {O} {_} {_} .proj₂ _ = tt
  ⊓y⊣y→ {I} {O} {_} .proj₂ _ = tt
  ⊓y⊣y→ {I} {I} {O} .proj₂ ()
  ⊓y⊣y→ {I} {I} {I} .proj₂ _ = tt
