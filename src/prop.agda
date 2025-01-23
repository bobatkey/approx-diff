{-# OPTIONS --prop --postfix-projections --safe #-}

module prop where

open import Level

data ⊥ {ℓ} : Prop ℓ where

record ⊤ {ℓ} : Prop ℓ where
  constructor tt

record LiftP {a} ℓ (A : Prop a) : Prop (a ⊔ ℓ) where
  constructor lift
  field
    lower : A
open LiftP public

data LiftS {a} ℓ (A : Set a) : Prop (a ⊔ ℓ) where
  liftS : A → LiftS ℓ A

record _∧_ {a b} (P : Prop a) (Q : Prop b) : Prop (a ⊔ b) where
  constructor _,_
  field
    proj₁ : P
    proj₂ : Q
open _∧_ public

record ∃ₚ {a b} (A : Prop a)(B : A → Prop b) : Prop (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
open ∃ₚ

data ∃ {a b} (A : Set a)(B : A → Prop b) : Prop (a ⊔ b) where
  exists : ∀ a → B a → ∃ A B

record Prf {ℓ} (P : Prop ℓ) : Set ℓ where
  constructor ⟪_⟫
  field
    prf : P
open Prf
