{-# OPTIONS --prop --postfix-projections --safe #-}

module label where

open import Level using (0ℓ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import prop
open import prop-setoid
  using (Setoid; IsEquivalence; ⊗-setoid; 𝟙; +-setoid)
  renaming (_⇒_ to _⇒s_)

open IsEquivalence

data label : Set where
  a b c d : label

data _≈_ : label → label → Prop where
  a : a ≈ a
  b : b ≈ b
  c : c ≈ c
  d : d ≈ d

≈-refl : ∀ {x} → x ≈ x
≈-refl {a} = a
≈-refl {b} = b
≈-refl {c} = c
≈-refl {d} = d

≈-sym : ∀ {x y} → x ≈ y → y ≈ x
≈-sym a = a
≈-sym b = b
≈-sym c = c
≈-sym d = d

≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
≈-trans a a = a
≈-trans b b = b
≈-trans c c = c
≈-trans d d = d

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence .refl = ≈-refl
≈-isEquivalence .sym = ≈-sym
≈-isEquivalence .trans = ≈-trans

Label : Setoid 0ℓ 0ℓ
Label .Setoid.Carrier = label
Label .Setoid._≈_ = _≈_
Label .Setoid.isEquivalence = ≈-isEquivalence

equal-label : ⊗-setoid Label Label ⇒s +-setoid (𝟙 {0ℓ} {0ℓ}) (𝟙 {0ℓ} {0ℓ})
equal-label ._⇒s_.func (a , a) = inj₁ _
equal-label ._⇒s_.func (b , b) = inj₁ _
equal-label ._⇒s_.func (c , c) = inj₁ _
equal-label ._⇒s_.func (d , d) = inj₁ _
equal-label ._⇒s_.func (_ , _) = inj₂ _
equal-label ._⇒s_.func-resp-≈ (a , a) = _
equal-label ._⇒s_.func-resp-≈ (a , b) = _
equal-label ._⇒s_.func-resp-≈ (a , c) = _
equal-label ._⇒s_.func-resp-≈ (a , d) = _
equal-label ._⇒s_.func-resp-≈ (b , a) = _
equal-label ._⇒s_.func-resp-≈ (b , b) = _
equal-label ._⇒s_.func-resp-≈ (b , c) = _
equal-label ._⇒s_.func-resp-≈ (b , d) = _
equal-label ._⇒s_.func-resp-≈ (c , a) = _
equal-label ._⇒s_.func-resp-≈ (c , b) = _
equal-label ._⇒s_.func-resp-≈ (c , c) = _
equal-label ._⇒s_.func-resp-≈ (c , d) = _
equal-label ._⇒s_.func-resp-≈ (d , a) = _
equal-label ._⇒s_.func-resp-≈ (d , b) = _
equal-label ._⇒s_.func-resp-≈ (d , c) = _
equal-label ._⇒s_.func-resp-≈ (d , d) = _
