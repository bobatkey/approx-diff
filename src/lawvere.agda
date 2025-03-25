{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (suc; _⊔_; Lift; lift; lower)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to 𝟙)
open import prop
open import prop-setoid using (IsEquivalence; module ≈-Reasoning)
open import basics
open import categories using (Category)
open import monoidal-product using (MonoidalProduct; SymmetricMonoidal)

module lawvere c
               {a₀ a b} {Ω : Set a} {_≤_ : Ω → Ω → Prop b}
               (≤-isPreorder : IsPreorder _≤_)
               {_•_ ε} (•-isMonoid : IsMonoid ≤-isPreorder _•_ ε)
               (•-comm : ∀ {x y} → (x • y) ≤ (y • x))
               {_-•_} (isResidual : IsResidual ≤-isPreorder •-isMonoid _-•_)
               {_∧_} (∧-isMeet : IsMeet ≤-isPreorder _∧_)
               {⋀} (⋀-isInf : IsBigMeet ≤-isPreorder (a₀ ⊔ b ⊔ c) ⋀)
  where

-- Categories of Lawvere metric spaces, generalised metric spaces
-- without symmetry(?). Preorders are these with Ω = Prop.

-- Basic idea: The order 'Ω' is a propositional logic, and Lawvere
-- spaces are “sets” with equality/order predicates valued in that
-- logic. Functions preserve the equality.

-- More generally, could use a hyperdoctrine? This would allow for
-- uniformly realisable implications.

-- We can also define predicates on a Space as predicates on elements
-- that are closed under addition.

-- I think these all give models of QTT as well? If we drop
-- reflexivity, then we get the ability to separate functions and
-- realisability.

-- Examples (all include symmetry, so might as well include it below)
--   - “Affine Logic for Constructive Mathematics”
--     Basically constructs the logic over Chu(Prop, ⊥)-sets
--   - “Induction and Recursion Principles in a Higher-Order Quantitative Logic” https://arxiv.org/pdf/2501.18275
--     Constructs a logic over [0,1]-sets
--   - Various step-indexed logics ("Logical Step-indexed Logical Relations"?, core Iris)
--     Constructs a logic over ωop-sets, here we want ultrametric spaces.
--     See also Ordered families of equivalences (OFEs), proposed by Di Gianantonio & Miculan (2002)
--   - Metric models of (total) Fuzz
--     [0,∞]-sets
--     - can this be combined with step-indexing to get a model of recursive fuzz?
--   - Security levels (e.g., “Modalities, Cohesion and Information Flow” by Alex Kavvos)
--     P(Level)-sets
--     I guess all of the cohesive structure from Alex's paper translates to the general setting?
--     - if we take copresheaves over Level-sets, then do we get something like Databases with permissions?
--       what does that mean for a query language?
--   - Setoids are Prop-valued sets.
--   - If we take the underlying preorder to be relations on a fixed set, then we'll get some more interesting connectives.

-- Would be interesting to see what completion means in all of these settings.

-- See also:
--   - “A Semantic Account of Metric Preservation” https://arxiv.org/pdf/1702.00374
--     This considers metrics on ωCPOs, for the purposes of modelling Fuzz

open IsPreorder ≤-isPreorder using ()
  renaming (refl to ≤-refl; trans to ≤-trans)

open IsMonoid •-isMonoid using ()
  renaming (mono to •-mono; lunit to •-lunit; runit to •-runit; assoc to •-assoc; interchange to •-interchange)

open IsBigMeet ⋀-isInf
  renaming (lower to ⋀-lower; greatest to ⋀-greatest)

------------------------------------------------------------------------------
record Spc : Set (suc a₀ ⊔ suc c ⊔ suc a ⊔ suc b) where
  no-eta-equality
  field
    Carrier : Set (c ⊔ a₀ ⊔ b)
    equal   : Carrier → Carrier → Ω
    refl    : ∀ {x} → ε ≤ equal x x
    sym     : ∀ {x y} → equal x y ≤ equal y x
    trans   : ∀ {x y z} → (equal x y • equal y z) ≤ equal x z

  _≃_ : Carrier → Carrier → Prop b
  x ≃ y = ε ≤ equal x y

  ≃-refl : ∀ {x} → x ≃ x
  ≃-refl = refl

  ≃-sym : ∀ {x y} → x ≃ y → y ≃ x
  ≃-sym ε≤eq-x-y = ≤-trans ε≤eq-x-y sym

  ≃-trans : ∀ {x y z} → x ≃ y → y ≃ z → x ≃ z
  ≃-trans ε≤eq-x-y ε≤eq-y-z =
    ≤-trans (•-lunit .proj₂) (≤-trans (•-mono ε≤eq-x-y ε≤eq-y-z) trans)

  ≃-isEquivalence : IsEquivalence _≃_
  ≃-isEquivalence .IsEquivalence.refl = refl
  ≃-isEquivalence .IsEquivalence.sym = ≃-sym
  ≃-isEquivalence .IsEquivalence.trans = ≃-trans

record _⇒_ (X Y : Spc) : Set (a₀ ⊔ b ⊔ c) where
  no-eta-equality
  private
    module X = Spc X
    module Y = Spc Y
  field
    fun    : X.Carrier → Y.Carrier
    preserve-eq : ∀ {x₁ x₂} → X.equal x₁ x₂ ≤ Y.equal (fun x₁) (fun x₂)

  preserve-≃ : ∀ {x₁ x₂} → x₁ X.≃ x₂ → fun x₁ Y.≃ fun x₂
  preserve-≃ x₁≃x₂ = ≤-trans x₁≃x₂ preserve-eq

record _≈_ {X Y} (f g : X ⇒ Y) : Prop (a₀ ⊔ b ⊔ c) where
  no-eta-equality
  open _⇒_
  private
    module X = Spc X
    module Y = Spc Y
  field
    f≈f : ∀ x → f .fun x Y.≃ g .fun x

module _ {X Y} where

  private
    module Y = Spc Y

  open _⇒_
  open _≈_

  ≈-refl : ∀ {f : X ⇒ Y} → f ≈ f
  ≈-refl .f≈f x = Y.≃-refl

  ≈-sym : ∀ {f g : X ⇒ Y} → f ≈ g → g ≈ f
  ≈-sym f≈g .f≈f x = Y.≃-sym (f≈g .f≈f x)

  ≈-trans : ∀ {f g h : X ⇒ Y} → f ≈ g → g ≈ h → f ≈ h
  ≈-trans f≈g g≈h .f≈f x = Y.≃-trans (f≈g .f≈f x) (g≈h .f≈f x)

  ≈-isEquivalence : IsEquivalence (_≈_ {X} {Y})
  ≈-isEquivalence .IsEquivalence.refl = ≈-refl
  ≈-isEquivalence .IsEquivalence.sym = ≈-sym
  ≈-isEquivalence .IsEquivalence.trans = ≈-trans

------------------------------------------------------------------------------
-- Category of Ω-Spaces
module _ where

  open Spc
  open _⇒_
  open _≈_

  id : ∀ X → X ⇒ X
  id X .fun x = x
  id X .preserve-eq = ≤-refl

  _∘_ : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
  (f ∘ g) .fun x = f .fun (g .fun x)
  _∘_ {X} {Y} {Z} f g .preserve-eq {x₁} {x₂} =
    begin
      X .equal x₁ x₂                   ≤⟨ g .preserve-eq ⟩
      Y .equal (g .fun x₁) (g .fun x₂) ≤⟨ f .preserve-eq ⟩
      Z .equal (f .fun (g .fun x₁)) (f .fun (g .fun x₂))
    ∎
    where open ≤-Reasoning ≤-isPreorder

  ∘-cong : ∀ {x y z} {f₁ f₂ : y ⇒ z} {g₁ g₂ : x ⇒ y} (f₁≈f₂ : f₁ ≈ f₂) (g₁≈g₂ : g₁ ≈ g₂) → (f₁ ∘ g₁) ≈ (f₂ ∘ g₂)
  ∘-cong {X} {Y} {Z} {f₁} f₁≈f₂ g₁≈g₂ .f≈f x =
    ≃-trans Z (preserve-≃ f₁ (g₁≈g₂ .f≈f x)) (f₁≈f₂ .f≈f _)

  cat : Category (suc c ⊔ suc a₀ ⊔ suc b ⊔ suc a) (c ⊔ a₀ ⊔ b) (c ⊔ a₀ ⊔ b)
  cat .Category.obj = Spc
  cat .Category._⇒_ = _⇒_
  cat .Category._≈_ = _≈_
  cat .Category.isEquiv = ≈-isEquivalence
  cat .Category.id = id
  cat .Category._∘_ = _∘_
  cat .Category.∘-cong = ∘-cong
  cat .Category.id-left {X} {Y} .f≈f x = ≃-refl Y
  cat .Category.id-right {X} {Y} .f≈f x = ≃-refl Y
  cat .Category.assoc {W} {X} {Y} {Z} f g h .f≈f x = ≃-refl Z

------------------------------------------------------------------------------
-- FIXME: Limits, which will be basically the same as those in Setoid

------------------------------------------------------------------------------
-- FIXME: Colimits

------------------------------------------------------------------------------
-- Functors to/from Setoid

-- Δ : Setoid → Spc, where equal x₁ x₂ = sup (x₁ ≈ x₂) (λ _ → ⊤)
-- ∇ : Setoid → Spc, where equal x₁ x₂ = ⊤
-- U : Spc → Setoid, where x₁ ≈ x₂ = ⊤ ≤ equal x₁ x₂
-- C : Spc → Setoid, where x₁ ≈ x₂ = ⊥ < equal x₁ x₂ -- i.e. “not disconnected”. Does this need the underlying order to have a strict <? or exists q, s.t. η q ≤ equal x₁ x₂
                                 -- or ∃ q. η q ≤ equal x₁ x₂
-- When do these yield LNL adjunctions? In fact, they presumably arise
-- from monotone functions between Prop and Ω. So it would be better
-- to generalise to any such functions.
--
--    For any preorder Ω, there are functions:
--      1. Ω → Prop = λ a → 1 ≤ a                   -- U
--      2. Prop → Ω = λ a → 1                       -- ∇
--      3. Prop → Ω = λ a → sup (Prf a) (λ _ → 1)   -- Δ
--      4. Ω → Prop = λ a → ∃ q. η(q) ≤ a                  -- 𝐂 ?????  needs a strict <
--    We are only interested in the ones that preserve being an
--    equivalence relation (that map ⊤ to ⊤, preserve meets? or preserve the monoid)
--
--    this is eerily similar to the LNL adjunction?
--
-- Conjecture: these form two Galois connections, which give some of
-- the pre-cohesive structure? What about connected components?


------------------------------------------------------------------------------
-- propositions, as a space

{-
module _ where
  open Spc

  proposition : Spc
  proposition .Carrier = Lift (a₀ ⊔ c ⊔ b) Ω
  proposition .equal (lift x) (lift y) = {!!} -- internal implication
  proposition .refl = {!!}
  proposition .trans = {!!}

  -- Predicates are then non-expansive functions X ⇒
  -- proposition. Entailment is via ordering of such functions
  -- (“natural transformations”).
  --
  -- All the relevant operations on 'Ω' get lifted to propositions.
  --
  -- And we get a (higher order?) logic “for free”. Presumably, we
  -- have to be careful with predicativity.
-}

------------------------------------------------------------------------------
-- (Symmetric) Monoidal Products from duoidal monoids.
--
-- What if x ∙ y = F(x • y)?
--
--  need (w ∙ x) • (y ∙ z) = F(w • x) • F(y • z) ≤ F(w • x • y • z) = (w • y) ∙ (x • z)
--   so F(x) • F(y) ≤ F(x • y) (monoidal endofunctor?)
module product {_∙_ : Ω → Ω → Ω} {ι : Ω}
               (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ι)
               (•-∙-duoidal : IsDuoidal ≤-isPreorder _•_ ε _∙_ ι)
               where

  open Spc
  open _⇒_
  open _≈_

  open IsDuoidal •-∙-duoidal
    renaming (gu to ε≤ι; mu to ι•ι≤ι; nu to ε≤ε∙ε)

  open IsMonoid ∙-isMonoid
    renaming (mono to ∙-mono; assoc to ∙-assoc; lunit to ∙-lunit; runit to ∙-runit)

  I : Spc
  I .Carrier = Lift _ 𝟙
  I .equal _ _ = ι
  I .refl = ε≤ι
  I .sym = ≤-refl
  I .trans = ι•ι≤ι

  _⊗_ : Spc → Spc → Spc
  (X ⊗ Y) .Carrier = X .Carrier × Y .Carrier
  (X ⊗ Y) .equal (x₁ , y₁) (x₂ , y₂) = X .equal x₁ x₂ ∙ Y .equal y₁ y₂
  (X ⊗ Y) .refl {x , y} =
    begin ε                           ≤⟨ ε≤ε∙ε ⟩
          ε ∙ ε                       ≤⟨ ∙-mono (X .refl) (Y .refl) ⟩
          X .equal x x ∙ Y .equal y y ∎
    where open ≤-Reasoning ≤-isPreorder
  (X ⊗ Y) .sym {x₁ , y₁} {x₂ , y₂} = ∙-mono (X .sym) (Y .sym)
  (X ⊗ Y) .trans {x₁ , y₁} {x₂ , y₂} {x₃ , y₃} =
    begin
      (X .equal x₁ x₂ ∙ Y .equal y₁ y₂) • (X .equal x₂ x₃ ∙ Y .equal y₂ y₃)
    ≤⟨ exchange ⟩
      (X .equal x₁ x₂ • X .equal x₂ x₃) ∙ (Y .equal y₁ y₂ • Y .equal y₂ y₃)
    ≤⟨ ∙-mono (X .trans) (Y .trans) ⟩
      X .equal x₁ x₃ ∙ Y .equal y₁ y₃
    ∎
    where open ≤-Reasoning ≤-isPreorder

  _⊗f_ : ∀ {X X' Y Y'} → X ⇒ X' → Y ⇒ Y' → (X ⊗ Y) ⇒ (X' ⊗ Y')
  (f ⊗f g) .fun (x , y)                = f .fun x , g .fun y
  (f ⊗f g) .preserve-eq {x₁ , y₁} {x₂ , y₂} = ∙-mono (f .preserve-eq) (g .preserve-eq)

  ⊗f-cong : ∀ {X X' Y Y'} {f₁ f₂ : X ⇒ X'} {g₁ g₂ : Y ⇒ Y'} → f₁ ≈ f₂ → g₁ ≈ g₂ → (f₁ ⊗f g₁) ≈ (f₂ ⊗f g₂)
  ⊗f-cong f₁≈f₂ g₁≈g₂ .f≈f (x , y) =
    ≤-trans ε≤ε∙ε (∙-mono (f₁≈f₂ .f≈f x) (g₁≈g₂ .f≈f y))

  -- Associativity
  assoc : ∀ {X Y Z} → ((X ⊗ Y) ⊗ Z) ⇒ (X ⊗ (Y ⊗ Z))
  assoc .fun ((x , y) , z) = x , (y , z)
  assoc .preserve-eq = ∙-assoc .proj₁

  assoc⁻¹ : ∀ {X Y Z} → (X ⊗ (Y ⊗ Z)) ⇒ ((X ⊗ Y) ⊗ Z)
  assoc⁻¹ .fun  (x , (y , z)) = ((x , y) , z)
  assoc⁻¹ .preserve-eq = ∙-assoc .proj₂

  lunit : ∀ {X} → (I ⊗ X) ⇒ X
  lunit .fun = proj₂
  lunit .preserve-eq = ∙-lunit .proj₁

  lunit⁻¹ : ∀ {X} → X ⇒ (I ⊗ X)
  lunit⁻¹ .fun x = lift tt , x
  lunit⁻¹ .preserve-eq = ∙-lunit .proj₂

  runit : ∀ {X} → (X ⊗ I) ⇒ X
  runit .fun = proj₁
  runit .preserve-eq = ∙-runit .proj₁

  runit⁻¹ : ∀ {X} → X ⇒ (X ⊗ I)
  runit⁻¹ .fun x = x , lift tt
  runit⁻¹ .preserve-eq = ∙-runit .proj₂

  monoidal : MonoidalProduct cat
  monoidal .MonoidalProduct.I⊗ = I
  monoidal .MonoidalProduct._⊗_ = _⊗_
  monoidal .MonoidalProduct._⊗m_ = _⊗f_
  monoidal .MonoidalProduct.⊗m-cong = ⊗f-cong
  monoidal .MonoidalProduct.⊗m-id {X} {Y} .f≈f (x , y) = ≃-refl (X ⊗ Y)
  monoidal .MonoidalProduct.⊗m-comp {X₁} {X₂} {Y₁} {Y₂} {Z₁} {Z₂} f₁ f₂ g₁ g₂ .f≈f (x₁ , x₂) = ≃-refl (Z₁ ⊗ Z₂)
  monoidal .MonoidalProduct.⊗-assoc = assoc
  monoidal .MonoidalProduct.⊗-assoc-natural {X₁} {X₂} {Y₁} {Y₂} {Z₁} {Z₂} f g h .f≈f ((x , y) , z) = ≃-refl (X₂ ⊗ (Y₂ ⊗ Z₂))
  monoidal .MonoidalProduct.⊗-assoc⁻¹ = assoc⁻¹
  monoidal .MonoidalProduct.⊗-assoc-iso1 {X} {Y} {Z} .f≈f (x , y , z) = ≃-refl (X ⊗ (Y ⊗ Z))
  monoidal .MonoidalProduct.⊗-assoc-iso2 {X} {Y} {Z} .f≈f ((x , y) , z) = ≃-refl ((X ⊗ Y) ⊗ Z)
  monoidal .MonoidalProduct.⊗-lunit = lunit
  monoidal .MonoidalProduct.⊗-lunit⁻¹ = lunit⁻¹
  monoidal .MonoidalProduct.⊗-lunit-natural {X₁} {X₂} f .f≈f x = ≃-refl X₂
  monoidal .MonoidalProduct.⊗-lunit-iso1 {X} .f≈f x = ≃-refl X
  monoidal .MonoidalProduct.⊗-lunit-iso2 {X} .f≈f x = ≃-refl (I ⊗ X)
  monoidal .MonoidalProduct.⊗-runit = runit
  monoidal .MonoidalProduct.⊗-runit⁻¹ = runit⁻¹
  monoidal .MonoidalProduct.⊗-runit-natural {X₁} {X₂} f .f≈f x = ≃-refl X₂
  monoidal .MonoidalProduct.⊗-runit-iso1 {X} .f≈f x = ≃-refl X
  monoidal .MonoidalProduct.⊗-runit-iso2 {X} .f≈f x = ≃-refl (X ⊗ I)
  monoidal .MonoidalProduct.pentagon {W} {X} {Y} {Z} .f≈f (((w , x) , y) , z) = ≃-refl (W ⊗ (X ⊗ (Y ⊗ Z)))
  monoidal .MonoidalProduct.triangle {X} {Y} .f≈f ((x , _) , y) = ≃-refl (X ⊗ Y)

  module _ (∙-comm : ∀ {x y} → (x ∙ y) ≤ (y ∙ x)) where

    -- Symmetry (if the original monoid is commutative)
    symmetry : ∀ {X Y} → (X ⊗ Y) ⇒ (Y ⊗ X)
    symmetry {X} {Y} .fun (x , y) = y , x
    symmetry {X} {Y} .preserve-eq {x₁ , y₁} {x₂ , y₂} = ∙-comm

    symmetric-monoidal : SymmetricMonoidal cat
    symmetric-monoidal .SymmetricMonoidal.monoidal = monoidal
    symmetric-monoidal .SymmetricMonoidal.⊗-symmetry = symmetry
    symmetric-monoidal .SymmetricMonoidal.⊗-symmetry-natural {X₁}{X₂}{Y₁}{Y₂} f g .f≈f (x , y) =
      (Y₂ ⊗ X₂) .refl
    symmetric-monoidal .SymmetricMonoidal.⊗-symmetry-iso {X}{Y} .f≈f (x , y) = (X ⊗ Y) .refl
    symmetric-monoidal .SymmetricMonoidal.⊗-symmetry-triangle {X} .f≈f (_ , x) = X .refl
    symmetric-monoidal .SymmetricMonoidal.⊗-symmetry-hexagon {X} {Y} {Z} .f≈f ((x , y) , z) =
      (Y ⊗ (Z ⊗ X)) .refl

open product •-isMonoid (selfDuoidal ≤-isPreorder •-isMonoid •-comm)
  renaming (symmetric-monoidal to symmetic-monoidal';
            symmetry to symmetry')
  public

⊗-symmetry = symmetry' •-comm
symmetric-monoidal = symmetic-monoidal' •-comm

------------------------------------------------------------------------------
-- The “native” products of the spaces is closed, so we have a
-- symmetric monoidal category.
module _ where

  open Spc
  open _⇒_
  open _≈_

  _⊸_ : Spc → Spc → Spc
  (X ⊸ Y) .Carrier = X ⇒ Y
  (X ⊸ Y) .equal f₁ f₂ = ⋀ (X .Carrier) λ x → Y .equal (f₁ .fun x) (f₂ .fun x)
  (X ⊸ Y) .refl = ⋀-greatest _ _ _ λ x → Y .refl
  (X ⊸ Y) .sym = ⋀-greatest _ _ _ λ x → ≤-trans (⋀-lower _ _ x) (Y .sym)
  (X ⊸ Y) .trans = ⋀-greatest _ _ _ λ x →
    ≤-trans (•-mono (⋀-lower _ _ x) (⋀-lower _ _ x)) (Y .trans)

  lambda : ∀ {X Y Z} → ((X ⊗ Y) ⇒ Z) → (X ⇒ (Y ⊸ Z))
  lambda {X} {Y} {Z} f .fun x .fun y = f .fun (x , y)
  lambda {X} {Y} {Z} f .fun x .preserve-eq =
    ≤-trans (•-lunit .proj₂) (≤-trans (•-mono (X .refl) ≤-refl) (f .preserve-eq))
  lambda {X} {Y} {Z} f .preserve-eq =
    ⋀-greatest _ _ _ λ y →
      ≤-trans (•-runit .proj₂) (≤-trans (•-mono ≤-refl (Y .refl)) (f .preserve-eq))

  lambda-cong : ∀ {X Y Z} {f₁ f₂ : (X ⊗ Y) ⇒ Z} → f₁ ≈ f₂ → lambda f₁ ≈ lambda f₂
  lambda-cong {X} {Y} {Z} {f₁} {f₂} f₁≈f₂ .f≈f x = ⋀-greatest _ _ _ λ y → f₁≈f₂ .f≈f (x , y)

  eval : ∀ {X Y} → ((X ⊸ Y) ⊗ X) ⇒ Y
  eval {X} {Y} .fun (f , x) = f .fun x
  eval {X} {Y} .preserve-eq {f₁ , x₁} {f₂ , x₂} =
    ≤-trans (mono (⋀-lower _ _ x₁) (f₂ .preserve-eq)) (Y .trans)
    where open IsMonoid •-isMonoid

  -- FIXME: lambda-eval equations

------------------------------------------------------------------------------
-- FIXME: cartesian products

-- Applying the monoidal product construction to the meets gives a
-- cartesian monoidal product, with duplication and units.

------------------------------------------------------------------------------
-- Later modalities
module Later
          (▷      : Ω → Ω)
          (▷-mono : ∀ {x y} → x ≤ y → ▷ x ≤ ▷ y)
          (▷-ε    : ε ≤ ▷ ε)
          (▷-•    : ∀ {x y} → (▷ x • ▷ y) ≤ ▷ (x • y))
         where

  open Spc
  open _⇒_

  L : Spc → Spc
  L X .Carrier = X .Carrier
  L X .equal x y = ▷ (X .equal x y)
  L X .refl = ≤-trans ▷-ε (▷-mono (X .refl))
  L X .sym = ▷-mono (X .sym)
  L X .trans = ≤-trans ▷-• (▷-mono (X .trans))
{-
  -- needs strength of ▷
  later : ∀ {X} → X ⇒ L X
  later .fun x = x
  later .preserve-eq = {!!}

  -- This will be true if:
  --  - X is Cauchy-complete
  --  - X is non-empty
  --  - It is possible to turn a function L X ⇒ X into a regular function
  fix : ∀ {X} → (L X ⇒ X) → I ⇒ X
  fix f = {!!}
-}
  -- For m ∈ Ω₀ and ϕ ∈ Ω, what is the n such that η m ≤ ▷^n ϕ ?
  -- Then, for an initial guess x₀, and ϕ = equal x₀ (f x₀), we can
  -- iterate f n many times to get the distance between successive
  -- approximations to be implied by η m.

  -- If x ∈ [0,1] and ▷ x = ½x, and m ∈ [0,1] ∩ ℚ, then need to solve
  --    (½)^n ≤ m
  --    1 ≤ 2^n m

------------------------------------------------------------------------------
-- Completion monad via regular functions.
module Completion {Ω₀ : Set a₀}
    (η : Ω₀ → Ω)
    (ε-isTop : IsTop ≤-isPreorder ε)
    (▷ : Ω₀ → Ω₀) (▷-split : ∀ {m} → η m ≤ (η (▷ m) • η (▷ m)))
    (approx : ∀ {x y} → (∀ m → x ≤ (η m -• y)) → x ≤ y)
  where

  open Spc
  open _⇒_
  open _≈_

  open IsResidual isResidual
    renaming (lambda to Ω-lambda; eval to Ω-eval)

  •-π₁ : ∀ {x y} → (x • y) ≤ x
  •-π₁ = ≤-trans (•-mono ≤-refl (ε-isTop .IsTop.≤-top)) (•-runit .proj₁)

  •-π₂ : ∀ {x y} → (x • y) ≤ y
  •-π₂ = ≤-trans (•-mono (ε-isTop .IsTop.≤-top) ≤-refl) (•-lunit .proj₁)

  η-▷ : ∀ {m} → η m ≤ η (▷ m)
  η-▷ {m} = begin
      η m               ≤⟨ ▷-split ⟩
      η (▷ m) • η (▷ m) ≤⟨ •-π₁ ⟩
      η (▷ m)           ∎
    where open ≤-Reasoning ≤-isPreorder

  record RegularFun (X : Spc) : Set (a₀ ⊔ b ⊔ c) where
    no-eta-equality
    field
      rfun    : Ω₀ → X .Carrier    -- Given an approximation level, give me a value
      regular : ∀ {m n} → (η m • η n) ≤ X .equal (rfun m) (rfun n)
  open RegularFun

  -- The additional η m is needed for the monad laws to hold
  _≃rf_ : ∀ {X} → RegularFun X → RegularFun X → Ω
  _≃rf_ {X} x y =
    ⋀ (Lift (b ⊔ c) (Ω₀ × Ω₀)) λ p →
      (η (p .lower .proj₁) • η (p .lower .proj₂)) -•
         X .equal (x .rfun (p .lower .proj₁)) (y .rfun (p .lower .proj₂))

  ≃rf-apply : ∀ {X} {x y : RegularFun X} {m n} → ((x ≃rf y) • (η m • η n)) ≤ X .equal (x .rfun m) (y .rfun n)
  ≃rf-apply {X} {x} {y} {m} {n} = ≤-trans (•-mono (⋀-lower _ _ (lift (m , n))) ≤-refl) Ω-eval

  ≃rf-intro : ∀ {X} {x y : RegularFun X} {z} →
              (∀ m n → (z • (η m • η n)) ≤ X .equal (x .rfun m) (y .rfun n)) →
              z ≤ (x ≃rf y)
  ≃rf-intro ϕ = ⋀-greatest _ _ _ λ { (lift (m , n)) → Ω-lambda (ϕ m n) }

  -- To what extent does this depend on the choice of ▷?
  𝐂 : Spc → Spc
  𝐂 X .Carrier = RegularFun X
  𝐂 X .equal = _≃rf_
  𝐂 X .refl {x} = ≃rf-intro {X} {x} {x} (λ _ _ → ≤-trans (•-lunit .proj₁) (x .regular))
  𝐂 X .sym {x} {y} = ⋀-greatest _ _ _ λ { (lift (m , n)) →
                        ≤-trans (⋀-lower _ _ (lift (n , m))) (-∙-mono •-comm (X .sym)) }
  𝐂 X .trans {x} {y} {z} =
      ⋀-greatest _ _ _ λ { (lift (m , n)) → approx λ p →
        Ω-lambda (Ω-lambda (begin
          (((x ≃rf y) • (y ≃rf z)) • η p) • (η m • η n)
        ≤⟨ •-assoc .proj₁ ⟩
          ((x ≃rf y) • (y ≃rf z)) • (η p • (η m • η n))
        ≤⟨ •-mono ≤-refl (•-mono ▷-split ≤-refl) ⟩
          ((x ≃rf y) • (y ≃rf z)) • ((η (▷ p) • η (▷ p)) • (η m • η n))
        ≤⟨ •-mono ≤-refl (•-interchange •-comm .proj₁) ⟩
          ((x ≃rf y) • (y ≃rf z)) • ((η (▷ p) • η m) • (η (▷ p) • η n))
        ≤⟨ •-interchange •-comm .proj₁ ⟩
          ((x ≃rf y) • (η (▷ p) • η m)) • ((y ≃rf z) • (η (▷ p) • η n))
        ≤⟨ •-mono (•-mono ≤-refl •-comm) ≤-refl ⟩
          ((x ≃rf y) • (η m • η (▷ p))) • ((y ≃rf z) • (η (▷ p) • η n))
        ≤⟨ •-mono (≃rf-apply {X} {x} {y}) (≃rf-apply {X} {y} {z}) ⟩
          X .equal (x .rfun m) (y .rfun (▷ p)) • X .equal (y .rfun (▷ p)) (z .rfun n)
        ≤⟨ X .trans ⟩
          X .equal (x .rfun m) (z .rfun n)
        ∎)) }
   where open ≤-Reasoning ≤-isPreorder

  𝐂-map : ∀ {X Y} → X ⇒ Y → 𝐂 X ⇒ 𝐂 Y
  𝐂-map f .fun x .rfun m = f .fun (x .rfun m)
  𝐂-map f .fun x .regular = ≤-trans (x .regular ) (f .preserve-eq)
  𝐂-map f .preserve-eq {x} {y} =
    ⋀-greatest _ _ _ λ { (lift (m , n)) → Ω-lambda (≤-trans (≃rf-apply {_} {x} {y}) (f .preserve-eq)) }

  open import functor using (Functor)

  𝐂-functor : Functor cat cat
  𝐂-functor .Functor.fobj = 𝐂
  𝐂-functor .Functor.fmor = 𝐂-map
  𝐂-functor .Functor.fmor-cong {X} {Y} {f₁} {f₂} f₁≈f₂ .f≈f x =
    ⋀-greatest _ _ _ λ { (lift (m , n )) → Ω-lambda (begin
       ε • (η m • η n)
     ≤⟨ •-mono ≤-refl (x .regular) ⟩
       ε • X .equal (x .rfun m) (x .rfun n)
     ≤⟨ •-mono (f₁≈f₂ .f≈f _) (f₂ .preserve-eq) ⟩
       Y .equal (f₁ .fun (x .rfun m)) (f₂ .fun (x .rfun m)) • Y .equal (f₂ .fun (x .rfun m)) (f₂ .fun (x .rfun n))
     ≤⟨ Y .trans ⟩
       Y .equal (f₁ .fun (x .rfun m)) (f₂ .fun (x .rfun n))
     ∎) }
    where open ≤-Reasoning ≤-isPreorder
  𝐂-functor .Functor.fmor-id {X} .f≈f x = 𝐂 X .refl {𝐂-map (id _) .fun x}
  𝐂-functor .Functor.fmor-comp {X} {Y} {Z} f g .f≈f x = 𝐂 Z .refl {𝐂-map (f ∘ g) .fun x}

  𝐂-unit : ∀ {X} → X ⇒ 𝐂 X
  𝐂-unit {X} .fun x .rfun _ = x
  𝐂-unit {X} .fun x .regular = ≤-trans (ε-isTop .IsTop.≤-top) (X .refl)
  𝐂-unit {X} .preserve-eq = ⋀-greatest _ _ _ λ { (lift (m , n)) → Ω-lambda •-π₁ }

  unit-natural : ∀ {X Y} (f : X ⇒ Y) → (𝐂-unit ∘ f) ≈ (𝐂-map f ∘ 𝐂-unit)
  unit-natural {X} {Y} f .f≈f x = 𝐂 Y .refl {𝐂-unit .fun (f .fun x)}

  𝐂-join : ∀ {X} → 𝐂 (𝐂 X) ⇒ 𝐂 X
  𝐂-join {X} .fun x .rfun m = x .rfun (▷ m) .rfun (▷ m)
  𝐂-join {X} .fun x .regular {m} {n} =
    begin
      η m • η n
    ≤⟨ •-mono ▷-split ▷-split ⟩
      (η (▷ m) • η (▷ m)) • (η (▷ n) • η (▷ n))
    ≤⟨ •-interchange •-comm .proj₁ ⟩
      (η (▷ m) • η (▷ n)) • (η (▷ m) • η (▷ n))
    ≤⟨ •-mono (x .regular {▷ m} {▷ n}) ≤-refl ⟩
      (x .rfun (▷ m) ≃rf x .rfun (▷ n)) • (η (▷ m) • η (▷ n))
    ≤⟨ ≃rf-apply {X} {x .rfun (▷ m)} {x .rfun (▷ n)} ⟩
      X .equal (x .rfun (▷ m) .rfun (▷ m)) (x .rfun (▷ n) .rfun (▷ n))
    ∎ where open ≤-Reasoning ≤-isPreorder
  𝐂-join {X} .preserve-eq {x} {y} =
    ⋀-greatest _ _ _ λ { (lift (m , n)) → Ω-lambda (begin
      (x ≃rf y) • (η m • η n)
    ≤⟨ •-mono ≤-refl (•-mono ▷-split ▷-split) ⟩
      (x ≃rf y) • ((η (▷ m) • η (▷ m)) • (η (▷ n) • η (▷ n)))
    ≤⟨ •-mono ≤-refl (•-interchange •-comm .proj₁) ⟩
      (x ≃rf y) • ((η (▷ m) • η (▷ n)) • (η (▷ m) • η (▷ n)))
    ≤⟨ •-assoc .proj₂ ⟩
      ((x ≃rf y) • (η (▷ m) • η (▷ n))) • (η (▷ m) • η (▷ n))
    ≤⟨ •-mono (≃rf-apply {𝐂 X} {x} {y}) ≤-refl ⟩
      (x .rfun (▷ m) ≃rf y .rfun (▷ n)) • (η (▷ m) • η (▷ n))
    ≤⟨ ≃rf-apply {X} {x .rfun (▷ m)} {y .rfun (▷ n)} ⟩
      X .equal (x .rfun (▷ m) .rfun (▷ m)) (y .rfun (▷ n) .rfun (▷ n))
    ∎) }
    where open ≤-Reasoning ≤-isPreorder

  join-natural : ∀ {X} {Y} (f : X ⇒ Y) → (𝐂-join ∘ 𝐂-map (𝐂-map f)) ≈ (𝐂-map f ∘ 𝐂-join)
  join-natural {X} {Y} f .f≈f x = 𝐂 Y .refl {𝐂-map f .fun (𝐂-join .fun x)}

  join-unit : ∀ {X} → (𝐂-join ∘ 𝐂-unit) ≈ id (𝐂 X)
  join-unit {X} .f≈f x = ⋀-greatest _ _ _ λ { (lift (m , n)) → Ω-lambda (≤-trans (•-lunit .proj₁)
                                                                         (≤-trans (•-mono η-▷ ≤-refl)
                                                                                  (x .regular {▷ m} {n}))) }

  join-𝐂unit : ∀ {X} → (𝐂-join ∘ 𝐂-map 𝐂-unit) ≈ id (𝐂 X)
  join-𝐂unit {X} .f≈f x = join-unit .f≈f x

  join-join : ∀ {X} → (𝐂-join ∘ 𝐂-map 𝐂-join) ≈ (𝐂-join ∘ 𝐂-join {𝐂 X})
  join-join {X} .f≈f x = ⋀-greatest _ _ _ λ { (lift (m , n)) → Ω-lambda (begin
      ε • (η m • η n)
    ≤⟨ •-lunit .proj₁ ⟩
      η m • η n
    ≤⟨ •-mono ▷-split ▷-split ⟩
      (η (▷ m) • η (▷ m)) • (η (▷ n) • η (▷ n))
    ≤⟨ •-interchange •-comm .proj₁ ⟩
      (η (▷ m) • η (▷ n)) • (η (▷ m) • η (▷ n))
    ≤⟨ •-mono (•-mono ≤-refl ▷-split) (•-mono ▷-split ≤-refl) ⟩
      (η (▷ m) • (η (▷ (▷ n)) • η (▷ (▷ n)))) • ((η (▷ (▷ m)) • η (▷ (▷ m))) • η (▷ n))
    ≤⟨ •-mono (•-assoc .proj₂) (•-assoc .proj₁) ⟩
      ((η (▷ m) • η (▷ (▷ n))) • η (▷ (▷ n))) • (η (▷ (▷ m)) • (η (▷ (▷ m)) • η (▷ n)))
    ≤⟨ •-mono (•-mono (x .regular {▷ m} {▷ (▷ n)}) ≤-refl) ≤-refl ⟩
      ((x .rfun (▷ m) ≃rf x .rfun (▷ (▷ n))) • η (▷ (▷ n))) • (η (▷ (▷ m)) • (η (▷ (▷ m)) • η (▷ n)))
    ≤⟨ •-interchange •-comm .proj₁ ⟩
      ((x .rfun (▷ m) ≃rf x .rfun (▷ (▷ n))) • η (▷ (▷ m))) • (η (▷ (▷ n)) • (η (▷ (▷ m)) • η (▷ n)))
    ≤⟨ •-assoc .proj₂ ⟩
      (((x .rfun (▷ m) ≃rf x .rfun (▷ (▷ n))) • η (▷ (▷ m))) • η (▷ (▷ n))) • (η (▷ (▷ m)) • η (▷ n))
    ≤⟨ •-mono (•-assoc .proj₁) ≤-refl ⟩
      ((x .rfun (▷ m) ≃rf x .rfun (▷ (▷ n))) • (η (▷ (▷ m)) • η (▷ (▷ n)))) • (η (▷ (▷ m)) • η (▷ n))
    ≤⟨ •-mono (≃rf-apply {𝐂 X} {x .rfun (▷ m)} {x .rfun (▷ (▷ n))}) ≤-refl ⟩
      (x .rfun (▷ m) .rfun (▷ (▷ m)) ≃rf x .rfun (▷ (▷ n)) .rfun (▷ (▷ n))) • (η (▷ (▷ m)) • η (▷ n))
    ≤⟨ ≃rf-apply {X} {x .rfun (▷ m) .rfun (▷ (▷ m))} {x .rfun (▷ (▷ n)) .rfun (▷ (▷ n))} ⟩
      X .equal (x .rfun (▷ m) .rfun (▷ (▷ m)) .rfun (▷ (▷ m))) (x .rfun (▷ (▷ n)) .rfun (▷ (▷ n)) .rfun (▷ n))
    ∎) }
    where open ≤-Reasoning ≤-isPreorder

  -- idempotency of the monad
  unit-join : ∀ {X} → (𝐂-unit ∘ 𝐂-join) ≈ id (𝐂 (𝐂 X))
  unit-join {X} .f≈f x =
    ⋀-greatest _ _ _ λ { (lift (m , n)) → Ω-lambda
      (⋀-greatest _ _ _ λ { (lift (m' , n')) → Ω-lambda (begin
          (ε • (η m • η n)) • (η m' • η n')
        ≤⟨ •-mono (•-lunit .proj₁) (•-mono ▷-split ≤-refl) ⟩
          (η m • η n) • ((η (▷ m') • η (▷ m')) • η n')
        ≤⟨ •-mono •-π₂ (•-assoc .proj₁) ⟩
          η n • (η (▷ m') • (η (▷ m') • η n'))
        ≤⟨ •-assoc .proj₂ ⟩
          (η n • η (▷ m')) • (η (▷ m') • η n')
        ≤⟨ •-mono •-comm ≤-refl ⟩
          (η (▷ m') • η n) • (η (▷ m') • η n')
        ≤⟨ •-mono (x .regular) ≤-refl ⟩
          (x .rfun (▷ m') ≃rf x .rfun n) • (η (▷ m') • η n')
        ≤⟨ ≃rf-apply {X} {x .rfun (▷ m')} {x .rfun n} ⟩
          X .equal (x .rfun (▷ m') .rfun (▷ m')) (x .rfun n .rfun n')
        ∎) }) }
    where open ≤-Reasoning ≤-isPreorder

  ------------------------------------------------------------------------------
  -- Complete Spaces have limits of regular functions.
  --
  -- FIXME: make this work for Cauchy sequences with a given modulus
  -- of continuity.
  module _ where

    -- A cauchy approximation is something that takes approximation
    -- bounds to elements satisfying a conditional equality.
    Approximation : ∀ X → (Ω₀ → X .Carrier) → Prop (a₀ ⊔ b)
    Approximation X x = ∀ m n → (η m • η n) ≤ X .equal (x m) (x n)

    IsLimit : ∀ X → (Ω₀ → X .Carrier) → X .Carrier → Prop (a₀ ⊔ b)
    IsLimit X x l = ∀ m → η m ≤ X .equal (x m) l

    IsLimit-natural : ∀ X Y x l (f : X ⇒ Y) →
                      IsLimit X x l → IsLimit Y (λ m → f .fun (x m)) (f .fun l)
    IsLimit-natural X Y x l f is-limit m =
      ≤-trans (is-limit m) (f .preserve-eq)

    IsLimit-≈ : ∀ {X x x' l} → (∀ m → _≃_ X (x m) (x' m)) → IsLimit X x' l → IsLimit X x l
    IsLimit-≈ {X} {x} {x'} {l} x≈x' is-limit m =
      ≤-trans (is-limit m) (≤-trans (•-lunit .proj₂) (≤-trans (•-mono (x≈x' m) ≤-refl) (X .trans)))

    lim : ∀ X x → Approximation X x → 𝐂 X .Carrier
    lim X x approx .rfun = x
    lim X x approx .regular {m} {n} = approx m n

    is-limit : ∀ X x (approx : Approximation X x) →
               IsLimit (𝐂 X) (λ m → 𝐂-unit .fun (x m)) (lim X x approx)
    is-limit X x approx m' = ⋀-greatest _ _ _ λ { (lift (m , n)) →
      Ω-lambda (≤-trans (•-mono ≤-refl •-π₂) (approx m' n)) }

    -- If the space 'X' has a 𝐂-algebra structure (which in the case
    -- of an idempotent monad means just the h-unit law), then it has
    -- limits of all Regular Functions.
    module _ (X : Spc) (h : 𝐂 X ⇒ X) (h-unit : (h ∘ 𝐂-unit) ≈ id _) where

      lim' : ∀ x → Approximation X x → X .Carrier
      lim' x approx = h .fun (lim X x approx)

      is-limit' : ∀ x (approx : Approximation X x) → IsLimit X x (lim' x approx)
      is-limit' x approx =
        IsLimit-≈ {X} (λ m → ≃-sym X (h-unit .f≈f (x m)))
          (IsLimit-natural (𝐂 X) X (λ m → 𝐂-unit .fun (x m)) (lim X x approx) h (is-limit X x approx))

  ------------------------------------------------------------------------------
  -- When are we guaranteed to get a Banach fixpoint combinator?
  --
  --   fix : (▷ X ⊸ X) ⇒ 𝐂 X
  --
  -- Given m and an initial x, we want to find a number of times to
  -- iterate f to get the distances below m. Some of this needs to be
  -- part of the data of the underlying logic and how ▷ interacts with
  -- everything else.

  ------------------------------------------------------------------------------
  -- Monoidal Monad: 𝐂 is a monoidal monad wrt the native monoidal
  -- product of the category.
--  open product •-isMonoid (selfDuoidal ≤-isPreorder •-isMonoid •-comm)

  monoidal-⊗ : ∀ {X Y} → (𝐂 X ⊗ 𝐂 Y) ⇒ 𝐂 (X ⊗ Y)
  monoidal-⊗ {X} {Y} .fun (x , y) .rfun m = x .rfun (▷ m) , y .rfun (▷ m)
  monoidal-⊗ {X} {Y} .fun (x , y) .regular {m} {n} = begin
      η m • η n
    ≤⟨ •-mono ▷-split ▷-split ⟩
      (η (▷ m) • η (▷ m)) • (η (▷ n) • η (▷ n))
    ≤⟨ •-interchange •-comm .proj₁ ⟩
      (η (▷ m) • η (▷ n)) • (η (▷ m) • η (▷ n))
    ≤⟨ •-mono (x .regular) (y .regular) ⟩
      X .equal (x .rfun (▷ m)) (x .rfun (▷ n)) • Y .equal (y .rfun (▷ m)) (y .rfun (▷ n))
    ∎
    where open ≤-Reasoning ≤-isPreorder
  monoidal-⊗ {X} {Y} .preserve-eq {x₁ , y₁} {x₂ , y₂} =
    ⋀-greatest _ _ _ λ { (lift (m , n)) → Ω-lambda (begin
      ((x₁ ≃rf x₂) • (y₁ ≃rf y₂)) • (η m • η n)
    ≤⟨ •-mono ≤-refl (•-mono ▷-split ▷-split) ⟩
      ((x₁ ≃rf x₂) • (y₁ ≃rf y₂)) • ((η (▷ m) • η (▷ m)) • (η (▷ n) • η (▷ n)))
    ≤⟨ •-mono ≤-refl (•-interchange •-comm .proj₁) ⟩
      ((x₁ ≃rf x₂) • (y₁ ≃rf y₂)) • ((η (▷ m) • η (▷ n)) • (η (▷ m) • η (▷ n)))
    ≤⟨ •-interchange •-comm .proj₁ ⟩
      ((x₁ ≃rf x₂) • (η (▷ m) • η (▷ n))) • ((y₁ ≃rf y₂) • (η (▷ m) • η (▷ n)))
    ≤⟨ •-mono (≃rf-apply {X} {x₁} {x₂}) (≃rf-apply {Y} {y₁} {y₂}) ⟩
      X .equal (x₁ .rfun (▷ m)) (x₂ .rfun (▷ n)) • Y .equal (y₁ .rfun (▷ m)) (y₂ .rfun (▷ n))
    ∎) }
    where open ≤-Reasoning ≤-isPreorder

{-
  -- Not sure this is true?
  monoidal-⊗⁻¹ : ∀ {X Y} → 𝐂 (X ⊗ Y) ⇒ (𝐂 X ⊗ 𝐂 Y)
  monoidal-⊗⁻¹ {X} {Y} .fun xy .proj₁ .rfun m = xy .rfun m .proj₁
  monoidal-⊗⁻¹ {X} {Y} .fun xy .proj₁ .regular {m} {n} = ≤-trans (xy .regular {m} {n}) •-π₁
  monoidal-⊗⁻¹ {X} {Y} .fun xy .proj₂ .rfun m = xy .rfun m .proj₂
  monoidal-⊗⁻¹ {X} {Y} .fun xy .proj₂ .regular {m} {n} = ≤-trans (xy .regular {m} {n}) •-π₂
  monoidal-⊗⁻¹ {X} {Y} .preserve-eq = {!!}
-}

  -- Naturality
  monoidal-natural : ∀ {X X' Y Y'} (f : X ⇒ X') (g : Y ⇒ Y') →
                     (monoidal-⊗ ∘ (𝐂-map f ⊗f 𝐂-map g)) ≈ (𝐂-map (f ⊗f g) ∘ monoidal-⊗)
  monoidal-natural {X} {X'} {Y} {Y'} f g .f≈f (x , y) =
    ⋀-greatest _ _ _ λ { (lift (m , n)) → Ω-lambda (begin
        ε • (η m • η n)
      ≤⟨ •-lunit .proj₁ ⟩
        η m • η n
      ≤⟨ •-mono ▷-split ▷-split ⟩
        (η (▷ m) • η (▷ m)) • (η (▷ n) • η (▷ n))
      ≤⟨ •-interchange •-comm .proj₁ ⟩
        (η (▷ m) • η (▷ n)) • (η (▷ m) • η (▷ n))
      ≤⟨ •-mono (x .regular) (y .regular) ⟩
        X .equal (x .rfun (▷ m)) (x .rfun (▷ n)) • Y .equal (y .rfun (▷ m)) (y .rfun (▷ n))
      ≤⟨ •-mono (f .preserve-eq) (g .preserve-eq) ⟩
        X' .equal (f .fun (x .rfun (▷ m))) (f .fun (x .rfun (▷ n))) • Y' .equal (g .fun (y .rfun (▷ m))) (g .fun (y .rfun (▷ n)))
      ∎) }
    where open ≤-Reasoning ≤-isPreorder

  -- 𝐂 commutes with associativity
  monoidal-assoc : ∀ {X Y Z} →
    (monoidal-⊗ ∘ ((id _ ⊗f monoidal-⊗) ∘ assoc {𝐂 X} {𝐂 Y} {𝐂 Z}))
    ≈ (𝐂-map assoc ∘ (monoidal-⊗ ∘ (monoidal-⊗ ⊗f id _)))
  monoidal-assoc {X} {Y} {Z} .f≈f ((x , y) , z) =
    ⋀-greatest _ _ _ λ { (lift (m , n)) → Ω-lambda (begin
      ε • (η m • η n)
    ≤⟨ •-lunit .proj₁ ⟩
      η m • η n
    ≤⟨ •-mono ▷-split ▷-split ⟩
      (η (▷ m) • η (▷ m)) • (η (▷ n) • η (▷ n))
    ≤⟨ •-interchange •-comm .proj₁ ⟩
      (η (▷ m) • η (▷ n)) • (η (▷ m) • η (▷ n))
    ≤⟨ •-mono (•-mono ≤-refl ▷-split) (•-mono ▷-split ≤-refl) ⟩
      (η (▷ m) • (η (▷ (▷ n)) • η (▷ (▷ n)))) • ((η (▷ (▷ m)) • η (▷ (▷ m))) • η (▷ n))
    ≤⟨ •-mono (•-assoc .proj₂) (•-assoc .proj₁) ⟩
      ((η (▷ m) • η (▷ (▷ n))) • η (▷ (▷ n))) • (η (▷ (▷ m)) • (η (▷ (▷ m)) • η (▷ n)))
    ≤⟨ •-interchange •-comm .proj₁ ⟩
      ((η (▷ m) • η (▷ (▷ n))) • η (▷ (▷ m))) • (η (▷ (▷ n)) • (η (▷ (▷ m)) • η (▷ n)))
    ≤⟨ •-assoc .proj₁ ⟩
      (η (▷ m) • η (▷ (▷ n))) • (η (▷ (▷ m)) • (η (▷ (▷ n)) • (η (▷ (▷ m)) • η (▷ n))))
    ≤⟨ •-mono ≤-refl (•-assoc .proj₂) ⟩
      (η (▷ m) • η (▷ (▷ n))) • ((η (▷ (▷ m)) • η (▷ (▷ n))) • (η (▷ (▷ m)) • η (▷ n)))
    ≤⟨ •-mono (x .regular) (•-mono (y .regular) (z .regular)) ⟩
      X .equal (x .rfun (▷ m)) (x .rfun (▷ (▷ n))) • (Y .equal (y .rfun (▷ (▷ m))) (y .rfun (▷ (▷ n))) • Z .equal (z .rfun (▷ (▷ m))) (z .rfun (▷ n)))
    ∎) }
    where open ≤-Reasoning ≤-isPreorder

  -- FIXME: monoidal-symmetry

  -- monoidal-left-unit
  monoidal-left-unit : ∀ {X} → (monoidal-⊗ {I}{X} ∘ (𝐂-unit ⊗f id _)) ≈ (𝐂-map lunit⁻¹ ∘ lunit)
  monoidal-left-unit {X} .f≈f (lift tt , x) =
    ⋀-greatest _ _ _ λ { (lift (m , n)) → Ω-lambda (•-mono ≤-refl (begin
      η m • η n
    ≤⟨ •-mono η-▷ ≤-refl ⟩
      η (▷ m) • η n
    ≤⟨ x .regular ⟩
      X .equal (x .rfun (▷ m)) (x .rfun n)
    ∎)) }
    where open ≤-Reasoning ≤-isPreorder

  monoidal-right-unit : ∀ {X} → (monoidal-⊗ {X}{I} ∘ (id _ ⊗f 𝐂-unit)) ≈ (𝐂-map runit⁻¹ ∘ runit)
  monoidal-right-unit {X} .f≈f (x , lift tt) =
    ⋀-greatest _ _ _ λ { (lift (m , n)) → Ω-lambda (begin
      ε • (η m • η n)
    ≤⟨ •-lunit .proj₁ ⟩
      η m • η n
    ≤⟨ •-mono η-▷ ≤-refl ⟩
      η (▷ m) • η n
    ≤⟨ x .regular ⟩
      X .equal (x .rfun (▷ m)) (x .rfun n)
    ≤⟨ •-runit .proj₂ ⟩
      X .equal (x .rfun (▷ m)) (x .rfun n) • ε
    ∎) }
    where open ≤-Reasoning ≤-isPreorder

  -- monoidal-unit
  monoidal-unit : ∀ {X Y} → (monoidal-⊗ {X} {Y} ∘ (𝐂-unit ⊗f 𝐂-unit)) ≈ 𝐂-unit
  monoidal-unit {X} {Y} .f≈f (x , y) =
    ⋀-greatest _ _ _ λ { (lift (m , n)) → Ω-lambda (begin
      ε • (η m • η n)             ≤⟨ •-mono ≤-refl (ε-isTop .IsTop.≤-top) ⟩
      ε • ε                       ≤⟨ •-mono (X .refl) (Y .refl) ⟩
      X .equal x x • Y .equal y y
    ∎) }
    where open ≤-Reasoning ≤-isPreorder

  -- monoidal-join
  monoidal-join : ∀ {X Y} → (monoidal-⊗ {X}{Y} ∘ (𝐂-join ⊗f 𝐂-join)) ≈ (𝐂-join ∘ (𝐂-map monoidal-⊗ ∘ monoidal-⊗))
  monoidal-join {X} {Y} .f≈f (x , y) =
    ⋀-greatest _ _ _ λ { (lift (m , n)) → Ω-lambda (begin
      ε • (η m • η n)
    ≤⟨ •-lunit .proj₁ ⟩
      η m • η n
    ≤⟨ •-mono ▷-split ▷-split ⟩
      (η (▷ m) • η (▷ m)) • (η (▷ n) • η (▷ n))
    ≤⟨ •-interchange •-comm .proj₁ ⟩
      (η (▷ m) • η (▷ n)) • (η (▷ m) • η (▷ n))
    ≤⟨ •-mono (•-mono ▷-split ▷-split) (•-mono ▷-split ▷-split) ⟩
      ((η (▷ (▷ m)) • η (▷ (▷ m))) • (η (▷ (▷ n)) • η (▷ (▷ n)))) • ((η (▷ (▷ m)) • η (▷ (▷ m))) • (η (▷ (▷ n)) • η (▷ (▷ n))))
    ≤⟨ •-mono (•-interchange •-comm .proj₁) (•-interchange •-comm .proj₁) ⟩
      ((η (▷ (▷ m)) • η (▷ (▷ n))) • (η (▷ (▷ m)) • η (▷ (▷ n)))) • ((η (▷ (▷ m)) • η (▷ (▷ n))) • (η (▷ (▷ m)) • η (▷ (▷ n))))
    ≤⟨ •-mono (•-mono (x .regular) ≤-refl) (•-mono (y .regular) ≤-refl) ⟩
      ((x .rfun (▷ (▷ m)) ≃rf x .rfun (▷ (▷ n))) • (η (▷ (▷ m)) • η (▷ (▷ n)))) • ((y .rfun (▷ (▷ m)) ≃rf y .rfun (▷ (▷ n))) • (η (▷ (▷ m)) • η (▷ (▷ n))))
    ≤⟨ •-mono (≃rf-apply {X} {x .rfun (▷ (▷ m))} {x .rfun (▷ (▷ n))}) (≃rf-apply {Y} {y .rfun (▷ (▷ m))} {y .rfun (▷ (▷ n))}) ⟩
      X .equal (x .rfun (▷ (▷ m)) .rfun (▷ (▷ m))) (x .rfun (▷ (▷ n)) .rfun (▷ (▷ n))) • Y .equal (y .rfun (▷ (▷ m)) .rfun (▷ (▷ m))) (y .rfun (▷ (▷ n)) .rfun (▷ (▷ n)))
    ∎) }
    where open ≤-Reasoning ≤-isPreorder

------------------------------------------------------------------------------
-- coproducts, needs some kind of annihilator for •
{-
module _ (⊥ : Ω)
      -- and ⊥ is bottom, and x • ⊥ = ⊥ • x = ⊥
    where
  open Spc

  _++_ : Spc → Spc → Spc
  (X ++ Y) .Carrier = X .Carrier ⊎ Y .Carrier
  (X ++ Y) .equal (inj₁ x₁) (inj₁ x₂) = X .equal x₁ x₂
  (X ++ Y) .equal (inj₁ _ ) (inj₂ _ ) = ⊥
  (X ++ Y) .equal (inj₂ _ ) (inj₁ _ ) = ⊥
  (X ++ Y) .equal (inj₂ y₁) (inj₂ y₂) = Y .equal y₁ y₂
  (X ++ Y) .refl {inj₁ x} = X .refl
  (X ++ Y) .refl {inj₂ y} = Y .refl
  (X ++ Y) .sym {inj₁ x} {inj₁ x₁} = X .sym
  (X ++ Y) .sym {inj₁ x} {inj₂ y} = ≤-refl
  (X ++ Y) .sym {inj₂ y} {inj₁ x} = ≤-refl
  (X ++ Y) .sym {inj₂ y} {inj₂ y₁} = Y .sym
  (X ++ Y) .trans {inj₁ x} {inj₁ x₁} {inj₁ x₂} = X .trans
  (X ++ Y) .trans {inj₁ x} {inj₁ x₁} {inj₂ y} = {!!}
  (X ++ Y) .trans {inj₁ x} {inj₂ y} {inj₁ x₁} = {!!}
  (X ++ Y) .trans {inj₁ x} {inj₂ y} {inj₂ y₁} = {!!}
  (X ++ Y) .trans {inj₂ y} {inj₁ x} {inj₁ x₁} = {!!}
  (X ++ Y) .trans {inj₂ y} {inj₁ x} {inj₂ y₁} = {!!}
  (X ++ Y) .trans {inj₂ y} {inj₂ y₁} {inj₁ x} = {!!}
  (X ++ Y) .trans {inj₂ y} {inj₂ y₁} {inj₂ y₂} = Y .trans
-}

-- 3. Cartesian Products (special case of monoidal construction when monoid is ∧)
-- 4. Limits?
--      Basically the same as limits in preorder
-- 5. Colimits?
-- 8. Terms, indexed by the generators of the equivalence monoid
--       e.g., security algebras and probability monads
-- 9. Scaling/weights, if we have a semiring.

-- Completion:
--
-- 1. Assume some small monoidal order Ω⁰, which order ηs into Ω, preserving the monoid.
-- 2. Define the completion of X to have elements
--        f : Ω⁰ → X .Carrier   such that   ∀ {m n} → η (m + n) ≤ X .equal (f m) (f n)
--    with equivalence (f,g) = inf (Ω⁰ × Ω⁰) (λ (m , n) → η (m + n) ⊸ X .equal (f m) (g n))
--    will need to assume that for all x, inf Ω⁰ (λ m → η m ⊸ x) ≤ x
-- 3. then this ought to be an idempotent monad, if we assume 'half : Ω⁰ → Ω⁰' st 'half x + half x = x'
-- 4. and it ought to be monoidal.

------------------------------------------------------------------------------
-- Predicates
module _ where

  open Spc

  record Pred (X : Spc) : Set (c ⊔ b ⊔ a ⊔ a₀) where
    field
      predicate    : X .Carrier → Ω
      predicate-eq : ∀ {x₁ x₂} → (X .equal x₁ x₂ • predicate x₁) ≤ predicate x₂
  open Pred

{-
  _⊗p_ : ∀ {X Y} → Pred X → Pred Y → Pred (X ⊗ Y)
  (ϕ ⊗p ψ) .predicate (x , y) = (ϕ .predicate x) • (ψ .predicate y)
  (ϕ ⊗p ψ) .predicate-eq = {!!}
-}
  -- Implication of predicates, leading to a collection of orders
  -- indexed by spaces.

  -- All of the properties and structure of 'Ω' ought to carry over.

  -- We should also be able to do quantification? So we get a
  -- hyperdoctrine.

  -- Logic: Γ | ϕ ⊢ ψ, where ϕ and ψ are predicates over Γ.

  -- If we can express the convex algebras, then we have a new
  -- “guarded” quantifier, where guard the
  --
  --   ∫ : 𝔻 X × (X ⊸ prop) ⊸ prop
  --
  -- “Generalised Expectation”

{-
  Forall : ∀ {X Y} → Pred (X ⊗ Y) → Pred X
  Forall {X} {Y} ϕ .predicate x = ⋀ (Y .Carrier) λ y → ϕ .predicate (x , y)
  Forall {X} {Y} ϕ .predicate-mono =
    ⋀-greatest _ _ _ λ y → ≤-trans (mono (runit .proj₂) (⋀-lower _ _ y))
                           (≤-trans (mono (mono ≤-refl (Y .refl)) ≤-refl)
                                    (ϕ .predicate-mono))
    where open IsMonoid +-isMonoid
-}

  -- Presumably, this isn't actually a right adjoint? No projections,
  -- for a start.

  -- This ought to be enough to make a predicate logic like Bacci and
  -- Møgelberg's, but generic in the choice of underlying logic. For
  -- example, if the underlying logic is Shulman's Chu(⊥), then we get
  -- the antithesis interpretation.

------------------------------------------------------------------------------

-- the crucial quantitative realisability relation is:
--   d(α + γ, β) ≤ eval(e, v, v')
-- i.e., the difference in potential implies the evaluation.
-- except that 'eval(e, v, v')' is not a ℕ∞ proposition. It is the wrong way up!
--
-- Some kind of profunctor-like relationship?
--
-- evaluation is a three-place relation. Why isn't the metric? Spaces
-- with two carriers, and a three way relation? What are the axioms?
--
-- d(γ, α, β) ≤ eval(e, v, v')
