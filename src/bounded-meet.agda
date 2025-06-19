{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (suc; 0ℓ)

module bounded-meet where

open import prop using (proj₁; proj₂; _∧_; _,_; LiftS; liftS)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import basics using (IsPreorder)
open import prop-setoid using (IsEquivalence)
open import categories using (Category; HasProducts; HasExponentials)

------------------------------------------------------------------------------
-- FIXME: move this to basics?
module _ {A : Set} {_≤_ : A → A → Prop} (≤-isPreorder : IsPreorder _≤_) where

  record IsMeetOf (x y meet : A) : Prop where
    field
      lower₁   : meet ≤ x
      lower₂   : meet ≤ y
      greatest : ∀ {z} → z ≤ x → z ≤ y → z ≤ meet

  open IsPreorder ≤-isPreorder
    renaming (refl to ≤-refl; trans to ≤-trans)
    using (isEquivalence; _≃_)
  open IsEquivalence isEquivalence
    renaming (refl to ≃-refl; sym to ≃-sym; trans to ≃-trans)

  open IsMeetOf

  meet-unique : ∀ {x y m₁ m₂} → IsMeetOf x y m₁ → IsMeetOf x y m₂ → m₁ ≃ m₂
  meet-unique is-meet₁ is-meet₂ .proj₁ = is-meet₂ .greatest (is-meet₁ .lower₁) (is-meet₁ .lower₂)
  meet-unique is-meet₁ is-meet₂ .proj₂ = is-meet₁ .greatest (is-meet₂ .lower₁) (is-meet₂ .lower₂)

  record HasMeetOf (x y : A) : Set where
    field
      meet    : A
      is-meet : IsMeetOf x y meet

-- FIXME: might make sense to rephrase as preservation of “pullbacks”.

record BoundedMeet : Set (suc 0ℓ) where
  no-eta-equality
  field
    Carrier      : Set
    _≤_          : Carrier → Carrier → Prop
    ≤-isPreorder : IsPreorder _≤_
    bounded-∧    : ∀ {x y z} → x ≤ z → y ≤ z → HasMeetOf ≤-isPreorder x y

  open IsPreorder ≤-isPreorder
    renaming (refl to ≤-refl; trans to ≤-trans)
    using (isEquivalence; _≃_) public
  open IsEquivalence isEquivalence
    renaming (refl to ≃-refl; sym to ≃-sym; trans to ≃-trans) public
open BoundedMeet

record _=>_ (A B : BoundedMeet) : Set where
  open BoundedMeet
  private
    module A = BoundedMeet A
    module B = BoundedMeet B
  field
    fun  : A.Carrier → B.Carrier
    mono : ∀ {x₁ x₂} → A ._≤_ x₁ x₂ → B ._≤_ (fun x₁) (fun x₂)
    cm   : ∀ {x₁ x₂ x x₁∧x₂} (p₁ : x₁ A.≤ x) (p₂ : x₂ A.≤ x) →
             IsMeetOf A.≤-isPreorder x₁ x₂ x₁∧x₂ →
             IsMeetOf B.≤-isPreorder (fun x₁) (fun x₂) (fun x₁∧x₂)

  resp-≃ : ∀ {x₁ x₂} → x₁ A.≃ x₂ → fun x₁ B.≃ fun x₂
  resp-≃ x₁≃x₂ .proj₁ = mono (x₁≃x₂ .proj₁)
  resp-≃ x₁≃x₂ .proj₂ = mono (x₁≃x₂ .proj₂)
open _=>_

record _≃m_ {A B} (f g : A => B) : Prop where
  private
    module A = BoundedMeet A
    module B = BoundedMeet B
  field
    eqfun : ∀ x → f .fun x B.≃ g .fun x
open _≃m_

≃m-isEquivalence : ∀ {A B} → IsEquivalence (_≃m_ {A} {B})
≃m-isEquivalence {A} {B} .IsEquivalence.refl .eqfun x = B .≃-refl
≃m-isEquivalence {A} {B} .IsEquivalence.sym e .eqfun x = B .≃-sym (e .eqfun x)
≃m-isEquivalence {A} {B} .IsEquivalence.trans e₁ e₂ .eqfun x = B .≃-trans (e₁ .eqfun x) (e₂ .eqfun x)

-- TODO:
--  1. Identities and Composition
--  2. Equality of morphisms, and category laws
--  3. Products
--  4. Coproducts
--  5. Function spaces
--  6. Lifted booleans, and the OR examples

id : ∀ A → A => A
id A .fun = λ z → z
id A .mono = λ z → z
id A .cm = λ p₁ p₂ z → z

_∘_ : ∀ {X Y Z} → Y => Z → X => Y → X => Z
(f ∘ g) .fun = λ z → f .fun (g .fun z)
(f ∘ g) .mono = λ z → f .mono (g .mono z)
(f ∘ g) .cm = λ p₁ p₂ z → f .cm (g .mono p₁) (g .mono p₂) (g .cm p₁ p₂ z)

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat .Category.obj = BoundedMeet
cat .Category._⇒_ = _=>_
cat .Category._≈_ = _≃m_
cat .Category.isEquiv = ≃m-isEquivalence
cat .Category.id = id
cat .Category._∘_ = _∘_
cat .Category.∘-cong {A}{B}{C} {f₁ = f₁} f₁≃f₂ g₁≃g₂ .eqfun x =
  C .≃-trans (resp-≃ f₁ (g₁≃g₂ .eqfun x)) (f₁≃f₂ .eqfun _)
cat .Category.id-left {A} {B} .eqfun x = B .≃-refl
cat .Category.id-right {A} {B} .eqfun x = B .≃-refl
cat .Category.assoc {A}{B}{C}{D} f g h .eqfun x = D .≃-refl

------------------------------------------------------------------------------
open HasMeetOf
open IsMeetOf
open IsPreorder

------------------------------------------------------------------------------
-- Products

_[×]_ : BoundedMeet → BoundedMeet → BoundedMeet
(A [×] B) .Carrier = A .Carrier × B .Carrier
(A [×] B) ._≤_ (x₁ , y₁) (x₂ , y₂) = (A ._≤_ x₁ x₂) ∧ (B ._≤_ y₁ y₂)
(A [×] B) .≤-isPreorder .IsPreorder.refl = A .≤-refl , B .≤-refl
(A [×] B) .≤-isPreorder .IsPreorder.trans (x₁≤y₁ , x₂≤y₂) (y₁≤z₁ , y₂≤z₂) =
    A .≤-trans x₁≤y₁ y₁≤z₁ , B .≤-trans x₂≤y₂ y₂≤z₂
(A [×] B) .bounded-∧ {x₁ , y₁} {x₂ , y₂} {x , y} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) .meet =
  A .bounded-∧ x₁≤x x₂≤x .meet ,
  B .bounded-∧ y₁≤y y₂≤y .meet
(A [×] B) .bounded-∧ {x₁ , y₁} {x₂ , y₂} {x , y} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) .is-meet .lower₁ =
  A .bounded-∧ x₁≤x x₂≤x .is-meet .lower₁ ,
  B .bounded-∧ y₁≤y y₂≤y .is-meet .lower₁
(A [×] B) .bounded-∧ {x₁ , y₁} {x₂ , y₂} {x , y} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) .is-meet .lower₂ =
  A .bounded-∧ x₁≤x x₂≤x .is-meet .lower₂ ,
  B .bounded-∧ y₁≤y y₂≤y .is-meet .lower₂
(A [×] B) .bounded-∧ {x₁ , y₁} {x₂ , y₂} {x , y} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) .is-meet .greatest {xz , yz} (xz≤x₁ , yz≤y₁) (xz≤x₂ , yz≤y₂) =
  A .bounded-∧ _ _ .is-meet .greatest xz≤x₁ xz≤x₂ ,
  B .bounded-∧ _ _ .is-meet .greatest yz≤y₁ yz≤y₂

project₁ : ∀ {X Y} → (X [×] Y) => X
project₁ .fun = proj₁
project₁ .mono = proj₁
project₁ .cm {x₁ , y₁} {x₂ , y₂} {x , y} {x₁∧x₂ , y₁∧y₂} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) m .lower₁ = m .lower₁ .proj₁
project₁ .cm {x₁ , y₁} {x₂ , y₂} {x , y} {x₁∧x₂ , y₁∧y₂} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) m .lower₂ = m .lower₂ .proj₁
project₁ {X} {Y} .cm {x₁ , y₁} {x₂ , y₂} {x , y} {x₁∧x₂ , y₁∧y₂} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) m .greatest z≤x₁ z≤x₂ =
  m .greatest  (z≤x₁ , m .lower₁ .proj₂) (z≤x₂ , m .lower₂ .proj₂) .proj₁

project₂ : ∀ {X Y} → (X [×] Y) => Y
project₂ .fun = proj₂
project₂ .mono = proj₂
project₂ .cm {x₁ , y₁} {x₂ , y₂} {x , y} {x₁∧x₂ , y₁∧y₂} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) m .lower₁ = m .lower₁ .proj₂
project₂ .cm {x₁ , y₁} {x₂ , y₂} {x , y} {x₁∧x₂ , y₁∧y₂} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) m .lower₂ = m .lower₂ .proj₂
project₂ {X} {Y} .cm {x₁ , y₁} {x₂ , y₂} {x , y} {x₁∧x₂ , y₁∧y₂} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) m .greatest z≤y₁ z≤y₂ =
  m .greatest  (m .lower₁ .proj₁ , z≤y₁) (m .lower₂ .proj₁ , z≤y₂) .proj₂

pair : ∀ {X Y Z} → X => Y → X => Z → X => (Y [×] Z)
pair {X} {Y} {Z} f g .fun x = (f .fun x) , (g .fun x)
pair {X} {Y} {Z} f g .mono x₁≤x₂ = (f .mono x₁≤x₂) , (g .mono x₁≤x₂)
pair {X} {Y} {Z} f g .cm {x₁} {x₂} {x} x₁≤x x₂≤x m .lower₁ = f .cm x₁≤x x₂≤x m .lower₁ , g .cm x₁≤x x₂≤x m .lower₁
pair {X} {Y} {Z} f g .cm {x₁} {x₂} {x} x₁≤x x₂≤x m .lower₂ = f .cm x₁≤x x₂≤x m .lower₂ , g .cm x₁≤x x₂≤x m .lower₂
pair {X} {Y} {Z} f g .cm {x₁} {x₂} {x} x₁≤x x₂≤x m .greatest {y , z} (y≤fx₁ , z≤gx₁) (y≤fx₂ , z≤gx₂) =
  f .cm x₁≤x x₂≤x m .greatest y≤fx₁ y≤fx₂ ,
  g .cm x₁≤x x₂≤x m .greatest z≤gx₁ z≤gx₂

products : HasProducts cat
products .HasProducts.prod = _[×]_
products .HasProducts.p₁ = project₁
products .HasProducts.p₂ = project₂
products .HasProducts.pair = pair
products .HasProducts.pair-cong f₁≃f₂ g₁≃g₂ .eqfun x =
  (f₁≃f₂ .eqfun x .proj₁ , g₁≃g₂ .eqfun x .proj₁) ,
  (f₁≃f₂ .eqfun x .proj₂ , g₁≃g₂ .eqfun x .proj₂)
products .HasProducts.pair-p₁ {X}{Y}{Z} f g .eqfun x = Y .BoundedMeet.≃-refl
products .HasProducts.pair-p₂ {X}{Y}{Z} f g .eqfun x = Z .BoundedMeet.≃-refl
products .HasProducts.pair-ext {X}{Y}{Z} f .eqfun x =
  (Y .≤-refl , Z .≤-refl) ,
  (Y .≤-refl , Z .≤-refl)

------------------------------------------------------------------------------
[×]-meet : ∀ {X Y x₁ x₂ x₁∧x₂ y₁ y₂ y₁∧y₂} →
           IsMeetOf (X .≤-isPreorder) x₁ x₂ x₁∧x₂ →
           IsMeetOf (Y .≤-isPreorder) y₁ y₂ y₁∧y₂ →
           IsMeetOf ((X [×] Y) .≤-isPreorder) (x₁ , y₁) (x₂ , y₂) (x₁∧x₂ , y₁∧y₂)
[×]-meet m-x m-y .lower₁ = m-x .lower₁ , m-y .lower₁
[×]-meet m-x m-y .lower₂ = m-x .lower₂ , m-y .lower₂
[×]-meet m-x m-y .greatest {x , y} (x≤x₁ , y≤y₁) (x≤x₂ , y≤y₂) =
  (m-x .greatest x≤x₁ x≤x₂) , (m-y .greatest y≤y₁ y≤y₂)

≤-meet : ∀ {X x₁ x₂} → X ._≤_ x₁ x₂ → IsMeetOf (X .≤-isPreorder) x₁ x₂ x₁
≤-meet {X} x₁≤x₂ .lower₁ = X .≤-refl
≤-meet {X} x₁≤x₂ .lower₂ = x₁≤x₂
≤-meet {X} x₁≤x₂ .greatest z≤x₁ z≤x₂ = z≤x₁

meet-idem : ∀ {X x} → IsMeetOf (X .≤-isPreorder) x x x
meet-idem {X} .lower₁ = X .≤-refl
meet-idem {X} .lower₂ = X .≤-refl
meet-idem {X} .greatest z₁ z₂ = z₁

-- lemma : IsMeet x y x∧y  and IsMeet a b y and x ≤ b then IsMeet x b x∧y
--
--   c  ---  b  ---  e
--   |       |       |
--   a  ---  d  ---  f


lemma : ∀ {X a b c d e} → IsMeetOf (X .≤-isPreorder) a b c → IsMeetOf (X .≤-isPreorder) e d b → X ._≤_ a d → IsMeetOf (X .≤-isPreorder) a e c
lemma {X} m₁ m₂ a≤d .lower₁ = m₁ .lower₁
lemma {X} m₁ m₂ a≤d .lower₂ = X .≤-trans (m₁ .lower₂) (m₂ .lower₁)
lemma {X} m₁ m₂ a≤d .greatest z≤a z≤e = m₁ .greatest z≤a (m₂ .greatest z≤e (≤-isPreorder X .trans z≤a a≤d))

meet-swap : ∀ {X a b c} → IsMeetOf (X .≤-isPreorder) a b c → IsMeetOf (X .≤-isPreorder) b a c
meet-swap m .lower₁ = m .lower₂
meet-swap m .lower₂ = m .lower₁
meet-swap m .greatest z₁ z₂ = m .greatest z₂ z₁


------------------------------------------------------------------------------
-- Coproducts: TODO



------------------------------------------------------------------------------
-- Exponentials

record _≤st_ {X Y : BoundedMeet} (f g : X => Y) : Prop where
  private
    module X = BoundedMeet X
    module Y = BoundedMeet Y
  field
    ext    : ∀ {x} → f .fun x Y.≤ g .fun x
    stable : ∀ {x x'} → x X.≤ x' → IsMeetOf Y.≤-isPreorder (f .fun x') (g .fun x) (f .fun x)
open _≤st_

≃st-ext₀ : ∀ {X Y} {f g : X => Y} → f ≃m g → f ≤st g
≃st-ext₀ f≃g .ext = f≃g .eqfun _ .proj₁
≃st-ext₀ {X} {Y} {f} {g} f≃g .stable x≤x' .lower₁ = f .mono x≤x'
≃st-ext₀ {X} {Y} {f} {g} f≃g .stable x≤x' .lower₂ = f≃g .eqfun _ .proj₁
≃st-ext₀ {X} {Y} {f} {g} f≃g .stable x≤x' .greatest z≤fx' z≤gx = Y .≤-trans z≤gx (f≃g .eqfun _ .proj₂)

≃st-ext : ∀ {X Y} {f g : X => Y} → f ≃m g → f ≤st g ∧ g ≤st f
≃st-ext f≃g .proj₁ = ≃st-ext₀ f≃g
≃st-ext f≃g .proj₂ = ≃st-ext₀ (≃m-isEquivalence .IsEquivalence.sym f≃g)

≤st-refl : ∀ {X Y} {f : X => Y} → f ≤st f
≤st-refl {X} {Y} {f} .ext = Y .≤-refl
≤st-refl {X} {Y} {f} .stable x≤x' .lower₁ = f .mono x≤x'
≤st-refl {X} {Y} {f} .stable x≤x' .lower₂ = Y .≤-refl
≤st-refl {X} {Y} {f} .stable x≤x' .greatest z≤fx' z≤fx = z≤fx

≤st-trans : ∀ {X Y} {f g h : X => Y} → f ≤st g → g ≤st h → f ≤st h
≤st-trans {X} {Y} {f} {g} {h} f≤g g≤h .ext {x} = Y .≤-trans (f≤g .ext) (g≤h .ext)
≤st-trans {X} {Y} {f} {g} {h} f≤g g≤h .stable x≤x' .lower₁ = f .mono x≤x'
≤st-trans {X} {Y} {f} {g} {h} f≤g g≤h .stable x≤x' .lower₂ = Y .≤-trans (f≤g .ext) (g≤h .ext)
≤st-trans {X} {Y} {f} {g} {h} f≤g g≤h .stable x≤x' .greatest z≤fx' z≤hx =
  f≤g .stable x≤x' .greatest z≤fx' (g≤h .stable x≤x' .greatest (Y .≤-trans z≤fx' (f≤g .ext)) z≤hx)

[→]-∧ : ∀ {X Y} {f₁ f₂ g : X => Y} → f₁ ≤st g → f₂ ≤st g → X => Y
[→]-∧ {X} {Y} {f₁} {f₂} {g} f₁≤g f₂≤g .fun x = Y .bounded-∧ (f₁≤g .ext {x}) (f₂≤g .ext) .meet
[→]-∧ {X} {Y} {f₁} {f₂} {g} f₁≤g f₂≤g .mono {x₁}{x₂} x₁≤x₂ =
  Y .bounded-∧ (f₁≤g .ext {x₂}) (f₂≤g .ext) .is-meet .greatest
    (Y .≤-trans (Y .bounded-∧ (f₁≤g .ext {x₁}) (f₂≤g .ext) .is-meet .lower₁) (f₁ .mono x₁≤x₂))
    (Y .≤-trans (Y .bounded-∧ (f₁≤g .ext {x₁}) (f₂≤g .ext) .is-meet .lower₂) (f₂ .mono x₁≤x₂))
[→]-∧ {X} {Y} {f₁} {f₂} {g} f₁≤g f₂≤g .cm {x₁} {x₂} {x} {x₁∧x₂} x₁≤x x₂≤x m .lower₁ = [→]-∧ {X} {Y} {f₁} {f₂} {g} f₁≤g f₂≤g .mono (m .lower₁)
[→]-∧ {X} {Y} {f₁} {f₂} {g} f₁≤g f₂≤g .cm {x₁} {x₂} {x} {x₁∧x₂} x₁≤x x₂≤x m .lower₂ = [→]-∧ {X} {Y} {f₁} {f₂} {g} f₁≤g f₂≤g .mono (m .lower₂)
[→]-∧ {X} {Y} {f₁} {f₂} {g} f₁≤g f₂≤g .cm {x₁} {x₂} {x} {x₁∧x₂} x₁≤x x₂≤x m .greatest z≤⟨f₁∧f₂⟩x₁ z≤⟨f₁∧f₂⟩x₂ =
  Y .bounded-∧ (f₁≤g .ext {x₁∧x₂}) (f₂≤g .ext) .is-meet .greatest
    (f₁ .cm x₁≤x x₂≤x m .greatest
      (Y .≤-trans z≤⟨f₁∧f₂⟩x₁
                  (Y .bounded-∧ (f₁≤g .ext {x₁}) (f₂≤g .ext) .is-meet .lower₁))
      (Y .≤-trans z≤⟨f₁∧f₂⟩x₂
                  (Y .bounded-∧ (f₁≤g .ext {x₂}) (f₂≤g .ext) .is-meet .lower₁)))
    (f₂ .cm x₁≤x x₂≤x m .greatest
      (Y .≤-trans z≤⟨f₁∧f₂⟩x₁ (Y .bounded-∧ (f₁≤g .ext {x₁}) (f₂≤g .ext) .is-meet .lower₂))
      (Y .≤-trans z≤⟨f₁∧f₂⟩x₂ (Y .bounded-∧ (f₁≤g .ext {x₂}) (f₂≤g .ext) .is-meet .lower₂)))

_[→]_ : BoundedMeet → BoundedMeet → BoundedMeet
(X [→] Y) .Carrier = X => Y
(X [→] Y) ._≤_ f g = f ≤st g
(X [→] Y) .≤-isPreorder .refl = ≤st-refl
(X [→] Y) .≤-isPreorder .trans = ≤st-trans
(X [→] Y) .bounded-∧ {f₁}{f₂}{g} f₁≤g f₂≤g .meet = [→]-∧ f₁≤g f₂≤g
(X [→] Y) .bounded-∧ {f₁} {f₂} {g} f₁≤g f₂≤g .is-meet .lower₁ .ext {x} = Y .bounded-∧ (f₁≤g .ext {x}) (f₂≤g .ext) .is-meet .lower₁
(X [→] Y) .bounded-∧ {f₁} {f₂} {g} f₁≤g f₂≤g .is-meet .lower₁ .stable x≤x' .lower₁ = [→]-∧ f₁≤g f₂≤g .mono x≤x'
(X [→] Y) .bounded-∧ {f₁} {f₂} {g} f₁≤g f₂≤g .is-meet .lower₁ .stable x≤x' .lower₂ = Y .bounded-∧ (f₁≤g .ext) (f₂≤g .ext) .is-meet .lower₁
(X [→] Y) .bounded-∧ {f₁} {f₂} {g} f₁≤g f₂≤g .is-meet .lower₁ .stable {x} {x'} x≤x' .greatest z≤⟨f₁∧f₂⟩x' z≤f₁x =
  Y .bounded-∧ (f₁≤g .ext {x}) (f₂≤g .ext) .is-meet .greatest
    z≤f₁x
    (f₂≤g .stable x≤x' .greatest (Y .≤-trans z≤⟨f₁∧f₂⟩x' (Y .bounded-∧ _ _ .is-meet .lower₂))
                                 (Y .≤-trans z≤f₁x (f₁≤g .ext)))
(X [→] Y) .bounded-∧ {f₁} {f₂} {g} f₁≤g f₂≤g .is-meet .lower₂ .ext = Y .bounded-∧ _ _ .is-meet .lower₂
(X [→] Y) .bounded-∧ {f₁} {f₂} {g} f₁≤g f₂≤g .is-meet .lower₂ .stable {x} {x'} x≤x' .lower₁ = [→]-∧ f₁≤g f₂≤g .mono x≤x'
(X [→] Y) .bounded-∧ {f₁} {f₂} {g} f₁≤g f₂≤g .is-meet .lower₂ .stable {x} {x'} x≤x' .lower₂ = Y .bounded-∧ _ _ .is-meet .lower₂
(X [→] Y) .bounded-∧ {f₁} {f₂} {g} f₁≤g f₂≤g .is-meet .lower₂ .stable {x} {x'} x≤x' .greatest z≤⟨f₁∧f₂⟩x' z≤f₂x =
  Y .bounded-∧ (f₁≤g .ext {x}) (f₂≤g .ext) .is-meet .greatest
    (f₁≤g .stable x≤x' .greatest (Y .≤-trans z≤⟨f₁∧f₂⟩x' (Y .bounded-∧ _ _ .is-meet .lower₁))
                                 (Y .≤-trans z≤f₂x (f₂≤g .ext)))
    z≤f₂x
(X [→] Y) .bounded-∧ {f₁} {f₂} {g} f₁≤g f₂≤g .is-meet .greatest {h} h≤f₁ h≤f₂ .ext = Y .bounded-∧ (f₁≤g .ext) (f₂≤g .ext) .is-meet .greatest (h≤f₁ .ext) (h≤f₂ .ext)
(X [→] Y) .bounded-∧ {f₁} {f₂} {g} f₁≤g f₂≤g .is-meet .greatest {h} h≤f₁ h≤f₂ .stable x≤x' .lower₁ = h .mono x≤x'
(X [→] Y) .bounded-∧ {f₁} {f₂} {g} f₁≤g f₂≤g .is-meet .greatest {h} h≤f₁ h≤f₂ .stable x≤x' .lower₂ = Y .bounded-∧ (f₁≤g .ext) (f₂≤g .ext) .is-meet .greatest (h≤f₁ .ext) (h≤f₂ .ext)
(X [→] Y) .bounded-∧ {f₁} {f₂} {g} f₁≤g f₂≤g .is-meet .greatest {h} h≤f₁ h≤f₂ .stable x≤x' .greatest z≤hx' z≤⟨f₁∧f₂⟩x =
  h≤f₁ .stable x≤x' .greatest
    z≤hx'
    (Y .≤-trans z≤⟨f₁∧f₂⟩x (Y .bounded-∧ (f₁≤g .ext) (f₂≤g .ext) .is-meet .lower₁))

eval : ∀ {X Y} → ((X [→] Y) [×] X) => Y
eval {X} {Y} .fun (f , x) = f .fun x
eval {X} {Y} .mono {f₁ , x₁} {f₂ , x₂} (f₁≤f₂ , x₁≤x₂) = Y .≤-trans (f₁ .mono x₁≤x₂) (f₁≤f₂ .ext)
eval {X} {Y} .cm {f₁ , x₁} {f₂ , x₂} {f , x} {f₁∧f₂ , x₁∧x₂} (f₁≤f , x₁≤x) (f₂≤f , x₂≤x) m = ϕ
  where
    -- f₁∧f₂(x₁∧x₂) --- f₁∧f₂(x₁) --- f₁(x₁)
    --      |       ϕ₁      |     ϕ₂    |
    --   f₁∧f₂(x₂) ---- f₁∧f₂(x) ---  f₁(x)
    --      |       ϕ₃      |     ϕ₅    |
    --     f₂(x₂) ------ f₂(x) ------ f(x)

    ϕ₀ : IsMeetOf (X .≤-isPreorder) x₁ x₂ x₁∧x₂
    ϕ₀ .lower₁ = m .lower₁ .proj₂
    ϕ₀ .lower₂ = m .lower₂ .proj₂
    ϕ₀ .greatest z≤x₁ z≤x₂ = m .greatest (m .lower₁ .proj₁ , z≤x₁) (m .lower₂ .proj₁ , z≤x₂) .proj₂

    ϕ₁ : IsMeetOf (Y .≤-isPreorder) (f₁∧f₂ .fun x₁) (f₁∧f₂ .fun x₂) (f₁∧f₂ .fun x₁∧x₂)
    ϕ₁ = f₁∧f₂ .cm x₁≤x x₂≤x ϕ₀

    ϕ₂ : IsMeetOf (Y .≤-isPreorder) (f₁∧f₂ .fun x) (f₁ .fun x₁) (f₁∧f₂ .fun x₁)
    ϕ₂ = m .lower₁ .proj₁ .stable x₁≤x

    ϕ₁₂ : IsMeetOf (Y .≤-isPreorder) (f₁∧f₂ .fun x₂) (f₁ .fun x₁) (f₁∧f₂ .fun x₁∧x₂)
    ϕ₁₂ = lemma {Y} (meet-swap {Y} ϕ₁) (meet-swap {Y} ϕ₂) (f₁∧f₂ .mono x₂≤x)

    ϕ₃ : IsMeetOf (Y .≤-isPreorder) (f₁∧f₂ .fun x) (f₂ .fun x₂) (f₁∧f₂ .fun x₂)
    ϕ₃ = m .lower₂ .proj₁ .stable x₂≤x

    ϕ₄ : IsMeetOf ((X [→] Y) .≤-isPreorder) f₁ f₂ f₁∧f₂
    ϕ₄ .lower₁ = m .lower₁ .proj₁
    ϕ₄ .lower₂ = m .lower₂ .proj₁
    ϕ₄ .greatest z≤f₁ z≤f₂ = m .greatest (z≤f₁ , m .lower₁ .proj₂) (z≤f₂ , m .lower₂ .proj₂) .proj₁

    -- FIXME: this should be “by definition”
    ϕ₅ : IsMeetOf (Y .≤-isPreorder) (f₁ .fun x) (f₂ .fun x) (f₁∧f₂ .fun x)
    ϕ₅ .lower₁ = ϕ₄ .lower₁ .ext
    ϕ₅ .lower₂ = ϕ₄ .lower₂ .ext
    ϕ₅ .greatest z≤f₁x z≤f₂x =
      Y .≤-trans (Y .bounded-∧ _ _ .is-meet .greatest z≤f₁x z≤f₂x)
                 (meet-unique ((X [→] Y) .≤-isPreorder) ((X [→] Y) .bounded-∧ f₁≤f f₂≤f .is-meet) ϕ₄ .proj₁ .ext)

    ϕ₃₅ : IsMeetOf (Y .≤-isPreorder) (f₂ .fun x₂) (f₁ .fun x) (f₁∧f₂ .fun x₂)
    ϕ₃₅ = lemma {Y} (meet-swap {Y} ϕ₃) ϕ₅ (f₂ .mono x₂≤x)

    ϕ : IsMeetOf (Y .≤-isPreorder) (f₁ .fun x₁) (f₂ .fun x₂) (f₁∧f₂ .fun x₁∧x₂)
    ϕ = lemma {Y} (meet-swap {Y} ϕ₁₂) ϕ₃₅ (f₁ .mono x₁≤x)

lambda : ∀ {X Y Z} → (X [×] Y) => Z → X => (Y [→] Z)
lambda {X} f .fun x .fun y = f .fun (x , y)
lambda {X} f .fun x .mono y₁≤y₂ = f .mono (X .≤-refl , y₁≤y₂)
lambda {X} {Y} f .fun x .cm {y₁}{y₂}{y}{y₁∧y₂} y₁≤y y₂≤y m = f .cm (X .≤-refl , y₁≤y) (X .≤-refl , y₂≤y) ϕ
   where ϕ : IsMeetOf ((X [×] Y) .≤-isPreorder) (x , y₁) (x , y₂) (x , y₁∧y₂)
         ϕ .lower₁ = X .≤-refl , m .lower₁
         ϕ .lower₂ = X .≤-refl , m .lower₂
         ϕ .greatest {x₀ , y₀} (x₀≤x , y₀≤y₁) (x₀≤x , y₀≤y₂) = x₀≤x , m .greatest y₀≤y₁ y₀≤y₂
lambda {X} {Y} f .mono x₁≤x₂ .ext = f .mono (x₁≤x₂ , Y .≤-refl)
lambda {X} {Y} f .mono {x₁}{x₂} x₁≤x₂ .stable {y} {y'} y≤y' = f .cm (x₁≤x₂ , Y .≤-refl) (X .≤-refl , y≤y') ϕ
  where -- FIXME: separate pairing and trivial meet combinators
        ϕ : IsMeetOf ((X [×] Y) .≤-isPreorder) (x₁ , y') (x₂ , y) (x₁ , y)
        ϕ .lower₁ = X .≤-refl , y≤y'
        ϕ .lower₂ = x₁≤x₂ , Y .≤-refl
        ϕ .greatest {x₀ , y₀} (x₀≤x₁ , y₀≤y') (x₀≤x₂ , y₀≤y) = x₀≤x₁ , y₀≤y
lambda {X} {Y} {Z} f .cm {x₁} {x₂} {x} {x₁∧x₂} x₁≤x x₂≤x m .lower₁ .ext = f .mono (m .lower₁ , Y .≤-refl)
lambda {X} {Y} {Z} f .cm {x₁} {x₂} {x} {x₁∧x₂} x₁≤x x₂≤x m .lower₁ .stable y≤y' =
  f .cm (m .lower₁ , Y .≤-refl) (X .≤-refl , y≤y') ([×]-meet {X} {Y} (≤-meet {X} (m .lower₁)) (meet-swap {Y} (≤-meet {Y} y≤y')))
lambda {X} {Y} {Z} f .cm {x₁} {x₂} {x} {x₁∧x₂} x₁≤x x₂≤x m .lower₂ .ext = f .mono (m .lower₂ , Y .≤-refl)
lambda {X} {Y} {Z} f .cm {x₁} {x₂} {x} {x₁∧x₂} x₁≤x x₂≤x m .lower₂ .stable y≤y' =
  f .cm (m .lower₂ , Y .≤-refl) (X .≤-refl , y≤y') ([×]-meet {X} {Y} (≤-meet {X} (m .lower₂)) (meet-swap {Y} (≤-meet {Y} y≤y')))
lambda {X} {Y} {Z} f .cm {x₁} {x₂} {x} {x₁∧x₂} x₁≤x x₂≤x m .greatest {h} h≤fx₁ h≤fx₂ .ext {y} =
  f .cm (x₁≤x , Y .≤-refl) (x₂≤x , Y .≤-refl) ϕ .greatest (h≤fx₁ .ext) (h≤fx₂ .ext)
  where ϕ : IsMeetOf ((X [×] Y) .≤-isPreorder) (x₁ , y) (x₂ , y) (x₁∧x₂ , y)
        ϕ = [×]-meet {X} {Y} m (meet-idem {Y})
lambda {X} {Y} {Z} f .cm {x₁} {x₂} {x} {x₁∧x₂} x₁≤x x₂≤x m .greatest {h} h≤fx₁ h≤fx₂ .stable {y} {y'} y≤y' .lower₁ = h .mono y≤y'
lambda {X} {Y} {Z} f .cm {x₁} {x₂} {x} {x₁∧x₂} x₁≤x x₂≤x m .greatest {h} h≤fx₁ h≤fx₂ .stable {y} {y'} y≤y' .lower₂ =
  f .cm (x₁≤x , y≤y') (x₂≤x , y≤y') ϕ .greatest (h≤fx₁ .ext) (h≤fx₂ .ext)
  where ϕ : IsMeetOf ((X [×] Y) .≤-isPreorder) (x₁ , y) (x₂ , y) (x₁∧x₂ , y)
        ϕ = [×]-meet {X} {Y} m (meet-idem {Y})
lambda {X} {Y} {Z} f .cm {x₁} {x₂} {x} {x₁∧x₂} x₁≤x x₂≤x m .greatest {h} h≤fx₁ h≤fx₂ .stable {y} {y'} y≤y' .greatest z≤hy' z≤f⟨x₁∧x₂,y⟩ =
  h≤fx₁ .stable y≤y' .greatest z≤hy' (Z .≤-trans z≤f⟨x₁∧x₂,y⟩ (f .mono (m .lower₁ , Y .≤-refl)))

exponentials : HasExponentials cat products
exponentials .HasExponentials.exp = _[→]_
exponentials .HasExponentials.eval = eval
exponentials .HasExponentials.lambda = lambda
exponentials .HasExponentials.lambda-cong {X}{Y}{Z} f₁≃f₂ .eqfun x =
  ≃st-ext (record { eqfun = λ y → f₁≃f₂ .eqfun (x , y) })
exponentials .HasExponentials.eval-lambda {X}{Y}{Z} f .eqfun (x , y) =
  Z .BoundedMeet.≃-refl
exponentials .HasExponentials.lambda-ext {X}{Y}{Z} f .eqfun x =
  ≃st-ext (record { eqfun = λ y → Z .BoundedMeet.≃-refl })
