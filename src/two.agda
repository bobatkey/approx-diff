{-# OPTIONS --prop --postfix-projections --safe #-}
module two where

open import basics
open import preorder

data Two : Set where
  O I : Two

data _≤_ : Two → Two → Prop where
  O-bot : ∀ {x} → O ≤ x
  I-top : ∀ {x} → x ≤ I

≤-isPreorder : IsPreorder _≤_
≤-isPreorder .IsPreorder.refl {O} = O-bot
≤-isPreorder .IsPreorder.refl {I} = I-top
≤-isPreorder .IsPreorder.trans {O} _ _ = O-bot
≤-isPreorder .IsPreorder.trans {I} {O} {I} _ _ = I-top
≤-isPreorder .IsPreorder.trans {I} {I} {I} _ _ = I-top

_⊓_ : Two → Two → Two
O ⊓ O = O
O ⊓ I = O
I ⊓ O = O
I ⊓ I = I

⊓-isMeet : IsMeet (≤-isPreorder) _⊓_
⊓-isMeet .IsMeet.π₁ {O} {O} = O-bot
⊓-isMeet .IsMeet.π₁ {O} {I} = O-bot
⊓-isMeet .IsMeet.π₁ {I} {O} = O-bot
⊓-isMeet .IsMeet.π₁ {I} {I} = I-top
⊓-isMeet .IsMeet.π₂ {O} {O} = O-bot
⊓-isMeet .IsMeet.π₂ {O} {I} = O-bot
⊓-isMeet .IsMeet.π₂ {I} {O} = O-bot
⊓-isMeet .IsMeet.π₂ {I} {I} = I-top
⊓-isMeet .IsMeet.⟨_,_⟩ {O} _ _ = O-bot
⊓-isMeet .IsMeet.⟨_,_⟩ {I} {I} {I} _ _ = I-top

_⊔_ : Two → Two → Two
O ⊔ O = O
O ⊔ I = I
I ⊔ O = I
I ⊔ I = I

⊔-isJoin : IsJoin (≤-isPreorder) _⊔_
⊔-isJoin .IsJoin.inl {O} {O} = O-bot
⊔-isJoin .IsJoin.inl {O} {I} = O-bot
⊔-isJoin .IsJoin.inl {I} {O} = I-top
⊔-isJoin .IsJoin.inl {I} {I} = I-top
⊔-isJoin .IsJoin.inr {O} {O} = O-bot
⊔-isJoin .IsJoin.inr {O} {I} = I-top
⊔-isJoin .IsJoin.inr {I} {O} = O-bot
⊔-isJoin .IsJoin.inr {I} {I} = I-top
⊔-isJoin .IsJoin.[_,_] {O} {O} _ _ = O-bot
⊔-isJoin .IsJoin.[_,_] {O} {I} {I} _ _ = I-top
⊔-isJoin .IsJoin.[_,_] {I} {O} {I} _ _ = I-top
⊔-isJoin .IsJoin.[_,_] {I} {I} {I} _ _ = I-top
