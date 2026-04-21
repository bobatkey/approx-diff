{-# OPTIONS --prop --postfix-projections --safe #-}
module two where

open import prop using (⊤; ⊥; tt; _∨_; inj₁; inj₂; _,_)
open import basics using (IsPreorder; IsMeet; IsJoin; IsBottom; IsTop)

data Two : Set where
  O I : Two

_≤_ : Two → Two → Prop
O ≤ y = ⊤
I ≤ O = ⊥
I ≤ I = ⊤

≤-refl : ∀ {x} → x ≤ x
≤-refl {O} = tt
≤-refl {I} = tt

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans {O} {O} {O} p q = tt
≤-trans {O} {O} {I} p q = tt
≤-trans {O} {I} {I} p q = tt
≤-trans {I} {I} {I} p q = tt

≤-total : ∀ x y → (x ≤ y) ∨ (y ≤ x)
≤-total O y = inj₁ tt
≤-total I O = inj₂ tt
≤-total I I = inj₁ tt

≤-isPreorder : IsPreorder _≤_
≤-isPreorder .IsPreorder.refl = ≤-refl
≤-isPreorder .IsPreorder.trans = ≤-trans

open IsPreorder ≤-isPreorder public

open import preorder using (Preorder)

Two-preorder : Preorder
Two-preorder .Preorder.Carrier = Two
Two-preorder .Preorder._≤_ = _≤_
Two-preorder .Preorder.≤-isPreorder = ≤-isPreorder

------------------------------------------------------------------------------
I-isTop : IsTop ≤-isPreorder I
I-isTop .IsTop.≤-top {O} = tt
I-isTop .IsTop.≤-top {I} = tt

_⊓_ : Two → Two → Two
O ⊓ x = O
I ⊓ x = x

⊓-lower₁ : ∀ {x y} → (x ⊓ y) ≤ x
⊓-lower₁ {O} {y} = tt
⊓-lower₁ {I} {y} = I-isTop .IsTop.≤-top

⊓-lower₂ : ∀ {x y} → (x ⊓ y) ≤ y
⊓-lower₂ {O} {y} = tt
⊓-lower₂ {I} {y} = ≤-refl

⊓-greatest : ∀ {x y z} → z ≤ x → z ≤ y → z ≤ (x ⊓ y)
⊓-greatest {x} {y} {O} tt tt = tt
⊓-greatest {I} {I} {I} tt tt = tt

⊓-isMeet : IsMeet ≤-isPreorder _⊓_
⊓-isMeet .IsMeet.π₁ = ⊓-lower₁
⊓-isMeet .IsMeet.π₂ = ⊓-lower₂
⊓-isMeet .IsMeet.⟨_,_⟩ = ⊓-greatest

------------------------------------------------------------------------------
O-isBottom : IsBottom ≤-isPreorder O
O-isBottom .IsBottom.≤-bottom = tt

_⊔_ : Two → Two → Two
O ⊔ x = x
I ⊔ x = I

⊔-upper₁ : ∀ {x y} → x ≤ (x ⊔ y)
⊔-upper₁ {O} {y} = tt
⊔-upper₁ {I} {y} = tt

⊔-upper₂ : ∀ {x y} → y ≤ (x ⊔ y)
⊔-upper₂ {O} {y} = ≤-refl
⊔-upper₂ {I} {y} = I-isTop .IsTop.≤-top

⊔-least : ∀ {x y z} → x ≤ z → y ≤ z → (x ⊔ y) ≤ z
⊔-least {O} {y} {z} p q = q
⊔-least {I} {y} {z} p q = p

⊔-isJoin : IsJoin ≤-isPreorder _⊔_
⊔-isJoin .IsJoin.inl = ⊔-upper₁
⊔-isJoin .IsJoin.inr = ⊔-upper₂
⊔-isJoin .IsJoin.[_,_] = ⊔-least

------------------------------------------------------------------------------
¬ : Two → Two
¬ O = I
¬ I = O

complement-∧ : ∀ {x} → (x ⊓ ¬ x) ≤ O
complement-∧ {O} = tt
complement-∧ {I} = tt

complement-∨ : ∀ {x} → I ≤ (x ⊔ ¬ x)
complement-∨ {O} = tt
complement-∨ {I} = tt

¬-involutive : ∀ {x} → x ≃ ¬ (¬ x)
¬-involutive {O} = ≃-refl {O}
¬-involutive {I} = ≃-refl {I}

¬-antitone : ∀ {x y} → x ≤ y → ¬ y ≤ ¬ x
¬-antitone {O} {O} _ = tt
¬-antitone {O} {I} _ = tt
¬-antitone {I} {I} _ = tt

-- FIXME: de Morgan, etc., should be derived from the fact that this
-- is a Boolean algebra.

------------------------------------------------------------------------------
-- Two as a commutative semiring (⊔, O, ⊓, I).

open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)

Two-setoid : Setoid _ _
Two-setoid .Setoid.Carrier = Two
Two-setoid .Setoid._≈_ = _≃_
Two-setoid .Setoid.isEquivalence = isEquivalence

open CommutativeMonoid

⊔-cmon : CommutativeMonoid Two-setoid
⊔-cmon .ε = O
⊔-cmon ._+_ = _⊔_
⊔-cmon .+-cong = IsJoin.cong ⊔-isJoin
⊔-cmon .+-lunit {x} = ≤-refl {x} , ≤-refl {x}
⊔-cmon .+-assoc {x} {y} {z} = IsJoin.assoc ⊔-isJoin {x} {y} {z}
⊔-cmon .+-comm {x} {y} = IsJoin.comm ⊔-isJoin {x} {y} , IsJoin.comm ⊔-isJoin {y} {x}

⊓-cmon : CommutativeMonoid Two-setoid
⊓-cmon .ε = I
⊓-cmon ._+_ = _⊓_
⊓-cmon .+-cong = IsMeet.cong ⊓-isMeet
⊓-cmon .+-lunit {x} = ≤-refl {x} , ≤-refl {x}
⊓-cmon .+-assoc {x} {y} {z} = IsMeet.assoc ⊓-isMeet {x} {y} {z}
⊓-cmon .+-comm {x} {y} = IsMeet.comm ⊓-isMeet {x} {y} , IsMeet.comm ⊓-isMeet {y} {x}

⊓-⊔-distribₗ : ∀ {x y z} → (x ⊓ (y ⊔ z)) ≃ ((x ⊓ y) ⊔ (x ⊓ z))
⊓-⊔-distribₗ {O} {y} {z} = ≤-refl {O} , ≤-refl {O}
⊓-⊔-distribₗ {I} {y} {z} = ≤-refl {y ⊔ z} , ≤-refl {y ⊔ z}

O-⊓-annihilₗ : ∀ {x} → (O ⊓ x) ≃ O
O-⊓-annihilₗ = ≤-refl {O} , ≤-refl {O}

open import commutative-monoid using (Idempotent)

⊔-idem : Idempotent ⊔-cmon
⊔-idem .Idempotent.+-idem {O} = ≤-refl {O} , ≤-refl {O}
⊔-idem .Idempotent.+-idem {I} = ≤-refl {I} , ≤-refl {I}

⊓-idem : Idempotent ⊓-cmon
⊓-idem .Idempotent.+-idem {O} = ≤-refl {O} , ≤-refl {O}
⊓-idem .Idempotent.+-idem {I} = ≤-refl {I} , ≤-refl {I}

semiring : CommutativeSemiring Two-setoid
semiring .CommutativeSemiring.additive = ⊔-cmon
semiring .CommutativeSemiring.multiplicative = ⊓-cmon
semiring .CommutativeSemiring.·-+-distribₗ {x} {y} {z} = ⊓-⊔-distribₗ {x} {y} {z}
semiring .CommutativeSemiring.ε-annihilₗ {x} = O-⊓-annihilₗ {x}
