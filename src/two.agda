{-# OPTIONS --prop --postfix-projections --safe #-}
module two where

open import prop
open import basics

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

open IsPreorder ≤-isPreorder



------------------------------------------------------------------------------
I-top : ∀ {x} → x ≤ I
I-top {O} = tt
I-top {I} = tt

_⊓_ : Two → Two → Two
O ⊓ x = O
I ⊓ x = x

⊓-lower₁ : ∀ {x y} → (x ⊓ y) ≤ x
⊓-lower₁ {O} {y} = tt
⊓-lower₁ {I} {y} = I-top

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
O-bot : ∀ {x} → O ≤ x
O-bot = tt

_⊔_ : Two → Two → Two
O ⊔ x = x
I ⊔ x = I

⊔-upper₁ : ∀ {x y} → x ≤ (x ⊔ y)
⊔-upper₁ {O} {y} = tt
⊔-upper₁ {I} {y} = tt

⊔-upper₂ : ∀ {x y} → y ≤ (x ⊔ y)
⊔-upper₂ {O} {y} = ≤-refl
⊔-upper₂ {I} {y} = I-top

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

-- FIXME: de Morgan, etc.


------------------------------------------------------------------------------
-- XOR
_⊕_ : Two → Two → Two
O ⊕ x = x
I ⊕ x = ¬ x

------------------------------------------------------------------------------
-- This is just a copy of Prop: not interesting!
--
-- However, without the ⊥-closed part, it is a little more interesting.
record Prp : Set₁ where
  field
    contains : Two → Prop
    ≤-closed : ∀ {x y} → x ≤ y → contains y → contains x
    ⊥-closed : contains O
open Prp
