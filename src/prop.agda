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

------------------------------------------------------------------------------
-- Relations

_⊎R_ : ∀ {a b c d ℓ} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
       (R : A → C → Prop ℓ) (S : B → D → Prop ℓ) →
       A ⊎ B → C ⊎ D → Prop ℓ
(R ⊎R S) (inj₁ a) (inj₁ c) = R a c
(R ⊎R S) (inj₁ _) (inj₂ _) = ⊥
(R ⊎R S) (inj₂ _) (inj₁ _) = ⊥
(R ⊎R S) (inj₂ b) (inj₂ d) = S b d
