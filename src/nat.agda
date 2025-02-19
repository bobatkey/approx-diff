{-# OPTIONS --prop --postfix-projections --safe #-}

module nat where

open import Level using (0ℓ)
open import Data.Product using (_,_)
open import prop
open import basics
open import prop-setoid using (module ≈-Reasoning; Setoid; ⊗-setoid; 𝟙)
  renaming (_⇒_ to _⇒s_)

------------------------------------------------------------------------------
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

------------------------------------------------------------------------------
data _≤_ : ℕ → ℕ → Prop where
  0≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → succ m ≤ succ n

infix 4 _≤_

succ-increasing : ∀ {x} → x ≤ succ x
succ-increasing {zero}   = 0≤n
succ-increasing {succ x} = s≤s succ-increasing

≤-refl : ∀ {x} → x ≤ x
≤-refl {zero}   = 0≤n
≤-refl {succ x} = s≤s ≤-refl

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans 0≤n       y≤z       = 0≤n
≤-trans (s≤s x≤y) (s≤s y≤z) = s≤s (≤-trans x≤y y≤z)

≤-total : ∀ x y → (x ≤ y) ∨ (y ≤ x)
≤-total zero y = inj₁ 0≤n
≤-total (succ x) zero = inj₂ 0≤n
≤-total (succ x) (succ y) with ≤-total x y
... | inj₁ x≤y = inj₁ (s≤s x≤y)
... | inj₂ y≤x = inj₂ (s≤s y≤x)

≤-isPreorder : IsPreorder _≤_
≤-isPreorder .IsPreorder.refl = ≤-refl
≤-isPreorder .IsPreorder.trans = ≤-trans

open IsPreorder ≤-isPreorder
  using (_≃_; ≃-refl; ≃-sym; ≃-trans)
  renaming (isEquivalence to ≃-isEquivalence)
  public

≃-zero : zero ≃ zero
≃-zero .proj₁ = 0≤n
≃-zero .proj₂ = 0≤n

succ-cong : ∀ {x y} → x ≃ y → succ x ≃ succ y
succ-cong p .proj₁ = s≤s (proj₁ p)
succ-cong p .proj₂ = s≤s (proj₂ p)

ℕₛ : Setoid 0ℓ 0ℓ
ℕₛ .Setoid.Carrier = ℕ
ℕₛ .Setoid._≈_ = _≃_
ℕₛ .Setoid.isEquivalence = ≃-isEquivalence

------------------------------------------------------------------------------
-- Joins and Meets

_⊔_ : ℕ → ℕ → ℕ
zero   ⊔ y      = y
succ x ⊔ zero   = succ x
succ x ⊔ succ y = succ (x ⊔ y)

upper₁ : ∀ {x y} → x ≤ (x ⊔ y)
upper₁ {zero}   {y}      = 0≤n
upper₁ {succ x} {zero}   = ≤-refl
upper₁ {succ x} {succ y} = s≤s upper₁

upper₂ : ∀ {x y} → y ≤ (x ⊔ y)
upper₂ {zero}   {zero}   = 0≤n
upper₂ {zero}   {succ y} = ≤-refl
upper₂ {succ x} {zero}   = 0≤n
upper₂ {succ x} {succ y} = s≤s upper₂

⊔-least : ∀ {x y z} → x ≤ z → y ≤ z → (x ⊔ y) ≤ z
⊔-least 0≤n       y≤z       = y≤z
⊔-least (s≤s x≤z) 0≤n       = s≤s x≤z
⊔-least (s≤s x≤z) (s≤s y≤z) = s≤s (⊔-least x≤z y≤z)

-- FIXME: also have _⊎_ version of this
⊔-split : ∀ {x y z} → z ≤ (x ⊔ y) → (z ≤ x) ∨ (z ≤ y)
⊔-split {x} {y} {zero} z≤x⊔y = inj₁ 0≤n
⊔-split {zero} {y} {succ z} z≤x⊔y = inj₂ z≤x⊔y
⊔-split {succ x} {zero} {succ z} z≤x⊔y = inj₁ z≤x⊔y
⊔-split {succ x} {succ y} {succ z} (s≤s z≤x⊔y) with ⊔-split {x} {y} {z} z≤x⊔y
... | inj₁ x₁ = inj₁ (s≤s x₁)
... | inj₂ x₁ = inj₂ (s≤s x₁)

⊔-chooses : ∀ x y → (x ⊔ y ≤ x) ∨ (x ⊔ y ≤ y)
⊔-chooses zero y = inj₂ ≤-refl
⊔-chooses (succ x) zero = inj₁ ≤-refl
⊔-chooses (succ x) (succ y) with ⊔-chooses x y
... | inj₁ p = inj₁ (s≤s p)
... | inj₂ p = inj₂ (s≤s p)

_⊓_ : ℕ → ℕ → ℕ
zero   ⊓ y      = zero
succ x ⊓ zero   = zero
succ x ⊓ succ y = succ (x ⊓ y)

⊓-greatest : ∀ {x y z} → z ≤ x → z ≤ y → z ≤ (x ⊓ y)
⊓-greatest 0≤n z≤y = 0≤n
⊓-greatest (s≤s z≤x) (s≤s z≤y) = s≤s (⊓-greatest z≤x z≤y)

lower₁ : ∀ {x y} → (x ⊓ y) ≤ x
lower₁ {zero}   {y}      = 0≤n
lower₁ {succ x} {zero}   = 0≤n
lower₁ {succ x} {succ y} = s≤s lower₁

lower₂ : ∀ {x y} → (x ⊓ y) ≤ y
lower₂ {zero}   {y}      = 0≤n
lower₂ {succ x} {zero}   = 0≤n
lower₂ {succ x} {succ y} = s≤s lower₂

⊓-isMeet : IsMeet ≤-isPreorder _⊓_
⊓-isMeet .IsMeet.π₁ = lower₁
⊓-isMeet .IsMeet.π₂ = lower₂
⊓-isMeet .IsMeet.⟨_,_⟩ = ⊓-greatest

open IsMeet ⊓-isMeet
  using ()
  renaming (mono to ⊓-mono; cong to ⊓-cong; assoc to ⊓-assoc; idem to ⊓-idem)

⊓-chooses : ∀ x y → (x ≤ x ⊓ y) ∨ (y ≤ x ⊓ y)
⊓-chooses zero     y    = inj₁ 0≤n
⊓-chooses (succ x) zero = inj₂ 0≤n
⊓-chooses (succ x) (succ y) with ⊓-chooses x y
... | inj₁ p = inj₁ (s≤s p)
... | inj₂ p = inj₂ (s≤s p)

-- Distributivity: FIXME: follows from totality and monotonicity

⊓-⊔-distrib : ∀ x y z → x ⊓ (y ⊔ z) ≤ (x ⊓ y) ⊔ (x ⊓ z)
⊓-⊔-distrib zero     y        z        = ≤-refl
⊓-⊔-distrib (succ x) zero     z        = ≤-refl
⊓-⊔-distrib (succ x) (succ y) zero     = ≤-refl
⊓-⊔-distrib (succ x) (succ y) (succ z) = s≤s (⊓-⊔-distrib x y z)

⊔-⊓-distrib : ∀ x y z → (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z)
⊔-⊓-distrib zero     y        z        = ≤-refl
⊔-⊓-distrib (succ x) zero     zero     = s≤s lower₁
⊔-⊓-distrib (succ x) zero     (succ z) = s≤s lower₁
⊔-⊓-distrib (succ x) (succ y) zero     = s≤s lower₂
⊔-⊓-distrib (succ x) (succ y) (succ z) = s≤s (⊔-⊓-distrib x y z)

------------------------------------------------------------------------------
_+_ : ℕ → ℕ → ℕ
zero   + y = y
succ x + y = succ (x + y)

+-increasing : ∀ {x y} → y ≤ (x + y)
+-increasing {zero} = ≤-refl
+-increasing {succ x} = ≤-trans succ-increasing (s≤s (+-increasing {x}))

+-mono : ∀ {x₁ x₂ y₁ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ + y₁) ≤ (x₂ + y₂)
+-mono 0≤n     0≤n     = 0≤n
+-mono 0≤n     (s≤s q) = ≤-trans (s≤s q) +-increasing
+-mono (s≤s p) q       = s≤s (+-mono p q)

+-lunit : ∀ {x} → (zero + x) ≃ x
+-lunit = ≃-refl

+-runit : ∀ {x} → (x + zero) ≃ x
+-runit {zero}   = ≃-zero
+-runit {succ x} = succ-cong +-runit

+-assoc : ∀ {x y z} → ((x + y) + z) ≃ (x + (y + z))
+-assoc {zero}   = ≃-refl
+-assoc {succ x} = succ-cong (+-assoc {x})

+-isMonoid : IsMonoid ≤-isPreorder _+_ zero
+-isMonoid .IsMonoid.mono = +-mono
+-isMonoid .IsMonoid.assoc {x} {y} {z} = +-assoc {x} {y} {z}
+-isMonoid .IsMonoid.lunit = +-lunit
+-isMonoid .IsMonoid.runit = +-runit

open IsMonoid +-isMonoid
  using ()
  renaming (cong to +-cong; interchange to +-interchange)

+-succ : ∀ {x y} → (x + succ y) ≃ succ (x + y)
+-succ {zero}   = succ-cong ≃-refl
+-succ {succ x} = succ-cong +-succ

+-comm : ∀ {x y} → (x + y) ≃ (y + x)
+-comm {zero}   = ≃-sym +-runit
+-comm {succ x} = ≃-trans (succ-cong (+-comm {x})) (≃-sym +-succ)

+-cancelₗ : ∀ {x y z} → (x + y) ≤ (x + z) → y ≤ z
+-cancelₗ {zero}   p       = p
+-cancelₗ {succ x} (s≤s p) = +-cancelₗ p

+-cancelᵣ : ∀ {x y z} → (y + x) ≤ (z + x) → y ≤ z
+-cancelᵣ {x}{y}{z} p =
  +-cancelₗ (≤-trans (+-comm {x} {y} .proj₁) (≤-trans p (+-comm {x} {z} .proj₂)))

-- Follows from totality and increasingness
⊓≤+ : ∀ {x y} → x ⊓ y ≤ x + y
⊓≤+ {zero}   {y}      = 0≤n
⊓≤+ {succ x} {zero}   = 0≤n
⊓≤+ {succ x} {succ y} = s≤s (≤-trans ⊓≤+ (+-mono {x} ≤-refl succ-increasing))

-- Distributivity with _⊔_ and _⊓_, which follows from monotonicity of
-- _+_ and totality of the order. FIXME: abstract this, so it works
-- for all other distributivity properties.

+-⊓-distribₗ : ∀ x y z → (x + y) ⊓ (x + z) ≤ x + (y ⊓ z)
+-⊓-distribₗ x y z with ≤-total y z
... | inj₁ p = ≤-trans lower₁ (+-mono {x} ≤-refl (⊓-greatest ≤-refl p))
... | inj₂ p = ≤-trans lower₂ (+-mono {x} ≤-refl (⊓-greatest p ≤-refl))

+-⊓-distrib : ∀ x y z → x + (y ⊓ z) ≤ (x + y) ⊓ (x + z)
+-⊓-distrib x y z = ⊓-greatest (+-mono {x} ≤-refl lower₁) (+-mono {x} ≤-refl lower₂)

+-⊔-distrib : ∀ x y z → x + (y ⊔ z) ≤ (x + y) ⊔ (x + z)
+-⊔-distrib x y z with ≤-total y z
... | inj₁ p = ≤-trans (+-mono {x} ≤-refl (⊔-least p ≤-refl)) upper₂
... | inj₂ p = ≤-trans (+-mono {x} ≤-refl (⊔-least ≤-refl p)) upper₁

------------------------------------------------------------------------------
-- Monus (a residual for + on ℕ^op)
_∸_ : ℕ → ℕ → ℕ
x      ∸ zero   = x
zero   ∸ succ y = zero
succ x ∸ succ y = x ∸ y

eval : ∀ {x y} → y ≤ (x + (y ∸ x))
eval {zero}   {y}      = ≤-refl
eval {succ x} {zero}   = 0≤n
eval {succ x} {succ y} = s≤s (eval {x} {y})

lambda : ∀ {x y z} → x ≤ (y + z) → (x ∸ y) ≤ z
lambda {x}      {zero}   f       = f
lambda {zero}   {succ y} 0≤n     = 0≤n
lambda {succ x} {succ y} (s≤s f) = lambda f

-- Totality means that this is an op-pre-total order
pre-total : ∀ x y → (x ∸ y) ⊓ (y ∸ x) ≤ zero
pre-total x y with ≤-total x y
... | inj₁ x≤y = ≤-trans lower₁ (lambda (≤-trans x≤y (+-runit .proj₂)))
... | inj₂ y≤x = ≤-trans lower₂ (lambda (≤-trans y≤x (+-runit .proj₂)))

---------------------------------------------------------------------------------------
-- FIXME: probably worth making a helper function for
-- nullary/unary/binary operations on setoids.
module _ where

  open _⇒s_

  add : ⊗-setoid ℕₛ ℕₛ ⇒s ℕₛ
  add .func (x , y) = x + y
  add .func-resp-≈ (x₁≈x₂ , y₁≈y₂) = +-cong x₁≈x₂ y₁≈y₂

  zero-m : 𝟙 {0ℓ} {0ℓ} ⇒s ℕₛ
  zero-m .func x = zero
  zero-m .func-resp-≈ x = ≃-refl

------------------------------------------------------------------------------
-- Multiplication

_*_ : ℕ → ℕ → ℕ
zero   * y = zero
succ x * y = y + (x * y)

one : ℕ
one = succ zero

*-zero : ∀ {x} → (x * zero) ≃ zero
*-zero {zero}   = ≃-refl
*-zero {succ x} = *-zero {x}

*-succ : ∀ {x y} → (y * succ x) ≃ (y + (y * x))
*-succ {x} {zero} = ≃-refl
*-succ {x} {succ y} =
  begin succ (x + (y * succ x))  ≈⟨ succ-cong (+-cong ≃-refl (*-succ {x} {y})) ⟩
        succ (x + (y + (y * x))) ≈˘⟨ succ-cong (+-assoc {x} {y}) ⟩
        succ ((x + y) + (y * x)) ≈⟨ succ-cong (+-cong (+-comm {x} {y}) ≃-refl) ⟩
        succ ((y + x) + (y * x)) ≈⟨ succ-cong (+-assoc {y} {x}) ⟩
        succ (y + (x + (y * x))) ∎
  where open ≈-Reasoning ≃-isEquivalence

*-mono : ∀ {x₁ x₂ y₁ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ * y₁) ≤ (x₂ * y₂)
*-mono 0≤n         y₁≤y₂ = 0≤n
*-mono (s≤s x₁≤x₂) y₁≤y₂ = +-mono y₁≤y₂ (*-mono x₁≤x₂ y₁≤y₂)

*-lunit : ∀ {x} → (one * x) ≃ x
*-lunit = +-runit

*-runit : ∀ {x} → (x * one) ≃ x
*-runit {zero}   = ≃-zero
*-runit {succ x} = succ-cong *-runit

*-comm : ∀ {x y} → (x * y) ≃ (y * x)
*-comm {zero}   {y} = ≃-sym (*-zero {y})
*-comm {succ x} {y} = ≃-trans (+-cong ≃-refl (*-comm {x} {y})) (≃-sym (*-succ {x} {y}))

+-*-distribₗ : ∀ {x y z} → (x * (y + z)) ≃ ((x * y) + (x * z))
+-*-distribₗ {zero} = ≃-refl
+-*-distribₗ {succ x} {y} {z} =
  begin
    ((y + z) + (x * (y + z)))       ≈⟨ +-cong ≃-refl (+-*-distribₗ {x} {y} {z}) ⟩
    ((y + z) + ((x * y) + (x * z))) ≈⟨ +-interchange (λ {x} {y} → +-comm {x} {y} .proj₁) {y} {z} ⟩
    ((y + (x * y)) + (z + (x * z))) ∎
  where open ≈-Reasoning ≃-isEquivalence

+-*-distribᵣ : ∀ {x y z} → ((y + z) * x) ≃ ((y * x) + (z * x))
+-*-distribᵣ {x} {y} {z} =
  begin
    (y + z) * x       ≈⟨ *-comm {y + z} {x} ⟩
    x * (y + z)       ≈⟨ +-*-distribₗ {x} {y} {z} ⟩
    (x * y) + (x * z) ≈⟨ +-cong (*-comm {x} {y}) (*-comm {x} {z}) ⟩
    (y * x) + (z * x) ∎
  where open ≈-Reasoning ≃-isEquivalence

*-assoc : ∀ {x y z} → ((x * y) * z) ≃ (x * (y * z))
*-assoc {zero} = ≃-refl
*-assoc {succ x} {y} {z} =
  begin
    (y + (x * y)) * z       ≈⟨ +-*-distribᵣ {z} {y} {x * y} ⟩
    (y * z) + ((x * y) * z) ≈⟨ +-cong ≃-refl (*-assoc {x} {y} {z}) ⟩
    (y * z) + (x * (y * z)) ∎
  where open ≈-Reasoning ≃-isEquivalence

*-isMonoid : IsMonoid ≤-isPreorder _*_ one
*-isMonoid .IsMonoid.mono = *-mono
*-isMonoid .IsMonoid.assoc {x} {y} {z} = *-assoc {x} {y} {z}
*-isMonoid .IsMonoid.lunit = *-lunit
*-isMonoid .IsMonoid.runit = *-runit

-- “feedback with an initial state”
*-cancelᵣ : ∀ {x y z} → one ≤ x → (y * x) ≤ (z * x) → y ≤ z
*-cancelᵣ {succ x} {zero}   {z}      (s≤s p) 0≤n     = 0≤n
*-cancelᵣ {succ x} {succ y} {succ z} (s≤s p) (s≤s q) = s≤s (*-cancelᵣ (s≤s p) (+-cancelₗ q))

*-cancelₗ : ∀ {x y z} → one ≤ x → (x * y) ≤ (x * z) → y ≤ z
*-cancelₗ {x} {y} {z} one≤x xy≤xz =
  *-cancelᵣ one≤x (begin y * x ≤⟨ *-comm {y} .proj₁ ⟩
                         x * y ≤⟨ xy≤xz ⟩
                         x * z ≤⟨ *-comm {x} .proj₁ ⟩
                         z * x ∎)
  where open ≤-Reasoning ≤-isPreorder
