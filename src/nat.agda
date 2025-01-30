{-# OPTIONS --prop --postfix-projections --safe #-}

module nat where

open import Level using (0ℓ)
open import Data.Product using (_,_)
open import prop
open import prop-setoid
  using (Setoid; IsEquivalence; ⊗-setoid; 𝟙)
  renaming (_⇒_ to _⇒s_)

open IsEquivalence

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data _≈_ : ℕ → ℕ → Prop where
  zero : zero ≈ zero
  succ : ∀ {m n} → m ≈ n → succ m ≈ succ n

≈-refl : ∀ {n} → n ≈ n
≈-refl {zero} = zero
≈-refl {succ n} = succ (≈-refl {n})

≈-sym : ∀ {m n} → m ≈ n → n ≈ m
≈-sym zero = zero
≈-sym (succ p) = succ (≈-sym p)

≈-trans : ∀ {m n o} → m ≈ n → n ≈ o → m ≈ o
≈-trans zero zero = zero
≈-trans (succ p) (succ q) = succ (≈-trans p q)

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence .refl = ≈-refl
≈-isEquivalence .sym = ≈-sym
≈-isEquivalence .trans = ≈-trans

ℕₛ : Setoid 0ℓ 0ℓ
ℕₛ .Setoid.Carrier = ℕ
ℕₛ .Setoid._≈_ = _≈_
ℕₛ .Setoid.isEquivalence = ≈-isEquivalence

------------------------------------------------------------------------------
-- FIXME: ordering

------------------------------------------------------------------------------
_+_ : ℕ → ℕ → ℕ
zero   + y = y
succ x + y = succ (x + y)

+-cong : ∀ {x₁ x₂ y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → (x₁ + y₁) ≈ (x₂ + y₂)
+-cong zero     q = q
+-cong (succ p) q = succ (+-cong p q)

-- FIXME: probably worth making a helper function for binary
-- operations like this.
add : ⊗-setoid ℕₛ ℕₛ ⇒s ℕₛ
add ._⇒s_.func (x , y) = x + y
add ._⇒s_.func-resp-≈ (x₁≈x₂ , y₁≈y₂) = +-cong x₁≈x₂ y₁≈y₂

zero-m : 𝟙 {0ℓ} {0ℓ} ⇒s ℕₛ
zero-m ._⇒s_.func x = zero
zero-m ._⇒s_.func-resp-≈ x = zero
