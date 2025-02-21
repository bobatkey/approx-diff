{-# OPTIONS --prop --postfix-projections --safe #-}
module two where

open import basics
open import preorder

data Two : Set where
  O I : Two

data _≤_ : Two → Two → Prop where
  O≤x : ∀ {x} → O ≤ x
  x≤I : ∀ {x} → x ≤ I

≤-isPreorder : IsPreorder _≤_
≤-isPreorder .IsPreorder.refl {O} = O≤x
≤-isPreorder .IsPreorder.refl {I} = x≤I
≤-isPreorder .IsPreorder.trans {O} _ _ = O≤x
≤-isPreorder .IsPreorder.trans {I} {O} {I} _ _ = x≤I
≤-isPreorder .IsPreorder.trans {I} {I} {I} _ _ = x≤I

_⊓_ : Two → Two → Two
O ⊓ O = O
O ⊓ I = O
I ⊓ O = O
I ⊓ I = I

⊓-isMeet : IsMeet (≤-isPreorder) _⊓_
⊓-isMeet .IsMeet.π₁ {O} {O} = O≤x
⊓-isMeet .IsMeet.π₁ {O} {I} = O≤x
⊓-isMeet .IsMeet.π₁ {I} {O} = O≤x
⊓-isMeet .IsMeet.π₁ {I} {I} = x≤I
⊓-isMeet .IsMeet.π₂ {O} {O} = O≤x
⊓-isMeet .IsMeet.π₂ {O} {I} = O≤x
⊓-isMeet .IsMeet.π₂ {I} {O} = O≤x
⊓-isMeet .IsMeet.π₂ {I} {I} = x≤I
⊓-isMeet .IsMeet.⟨_,_⟩ {O} {O} {O} _ _ = O≤x
⊓-isMeet .IsMeet.⟨_,_⟩ {O} {O} {I} _ _ = O≤x
⊓-isMeet .IsMeet.⟨_,_⟩ {O} {I} {O} _ _ = O≤x
⊓-isMeet .IsMeet.⟨_,_⟩ {O} {I} {I} _ _ = O≤x
⊓-isMeet .IsMeet.⟨_,_⟩ {I} {I} {I} _ _ = x≤I

_⊔_ : Two → Two → Two
O ⊔ O = O
O ⊔ I = I
I ⊔ O = I
I ⊔ I = I

⊔-isJoin : IsJoin (≤-isPreorder) _⊔_
⊔-isJoin .IsJoin.inl {O} {O} = O≤x
⊔-isJoin .IsJoin.inl {O} {I} = O≤x
⊔-isJoin .IsJoin.inl {I} {O} = x≤I
⊔-isJoin .IsJoin.inl {I} {I} = x≤I
⊔-isJoin .IsJoin.inr {O} {O} = O≤x
⊔-isJoin .IsJoin.inr {O} {I} = x≤I
⊔-isJoin .IsJoin.inr {I} {O} = O≤x
⊔-isJoin .IsJoin.inr {I} {I} = x≤I
⊔-isJoin .IsJoin.[_,_] {O} {O} {O} _ _ = O≤x
⊔-isJoin .IsJoin.[_,_] {O} {O} {I} _ _ = O≤x
⊔-isJoin .IsJoin.[_,_] {O} {I} {I} _ _ = x≤I
⊔-isJoin .IsJoin.[_,_] {I} {O} {I} _ _ = x≤I
⊔-isJoin .IsJoin.[_,_] {I} {I} {I} _ _ = x≤I
