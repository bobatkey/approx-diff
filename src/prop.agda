{-# OPTIONS --prop --postfix-projections --safe #-}

module prop where

open import Level
open import Data.Sum using (_⊎_; inj₁; inj₂)

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

infixr 4 _∧_ _,_

data _∨_ {a b} (P : Prop a) (Q : Prop b) : Prop (a ⊔ b) where
  inj₁ : P → P ∨ Q
  inj₂ : Q → P ∨ Q

record ∃ₚ {a b} (A : Prop a)(B : A → Prop b) : Prop (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
open ∃ₚ

data ∃ {a b} (A : Set a)(B : A → Prop b) : Prop (a ⊔ b) where
  _,_ : ∀ a → B a → ∃ A B

record ∃ₛ {a b} (A : Set a)(B : A → Prop b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
open ∃ₚ

record Prf {ℓ} (P : Prop ℓ) : Set ℓ where
  constructor ⟪_⟫
  field
    prf : P
open Prf

module _ where
  infix 4 _⇔_

  _⇔_ : Prop → Prop → Prop
  P ⇔ Q = (P → Q) ∧ (Q → P)

  refl-⇔ : ∀ {P} → P ⇔ P
  refl-⇔ .proj₁ x = x
  refl-⇔ .proj₂ x = x

  trans-⇔ : ∀ {P Q R} → P ⇔ Q → Q ⇔ R → P ⇔ R
  trans-⇔ e₁ e₂ .proj₁ p = e₂ .proj₁ (e₁ .proj₁ p)
  trans-⇔ e₁ e₂ .proj₂ r = e₁ .proj₂ (e₂ .proj₂ r)

------------------------------------------------------------------------------
-- Relations

_⊎R_ : ∀ {a b c d ℓ} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
       (R : A → C → Prop ℓ) (S : B → D → Prop ℓ) →
       A ⊎ B → C ⊎ D → Prop ℓ
(R ⊎R S) (inj₁ a) (inj₁ c) = R a c
(R ⊎R S) (inj₁ _) (inj₂ _) = ⊥
(R ⊎R S) (inj₂ _) (inj₁ _) = ⊥
(R ⊎R S) (inj₂ b) (inj₂ d) = S b d
