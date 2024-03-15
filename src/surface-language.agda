{-# OPTIONS --postfix-projections --without-K --safe #-}

module surface-language where

open import Data.Nat using (ℕ)

data type : Set where
  unit num : type

infix 4 _∋_ _⊢_

data ctxt : Set where
  ε : ctxt
  _-,_ : ctxt → type → ctxt

data _∋_ : ctxt → type → Set where
  ze : ∀ {Γ τ} → Γ -, τ ∋ τ
  su : ∀ {Γ τ σ} → Γ ∋ τ → Γ -, σ ∋ τ

data _⊢_ : ctxt → type → Set where
  var : ∀ {Γ τ} → Γ ∋ τ → Γ ⊢ τ

  -- Natural numbers and some operations
  nat : ∀ {Γ} → ℕ -> Γ ⊢ num

  -- The sole value of the unit type
  unit : ∀ {Γ} → Γ ⊢ unit

import language as ML

⟦_⟧ₐty : type → ML.type
⟦ unit ⟧ₐty = ML.unit -- should probably be lifted
⟦ num ⟧ₐty = ML.lift ML.num

⟦_⟧ₐctxt : ctxt → ML.ctxt
⟦ ε ⟧ₐctxt      = ML.ε
⟦ Γ -, τ ⟧ₐctxt = ⟦ Γ ⟧ₐctxt ML.-, ⟦ τ ⟧ₐty

⟦_⟧ₐ∋ : ∀ {Γ σ} → Γ ∋ σ → ⟦ Γ ⟧ₐctxt ML.∋ ⟦ σ ⟧ₐty
⟦ ze ⟧ₐ∋ = ML.ze
⟦ su x ⟧ₐ∋ = ML.su ⟦ x ⟧ₐ∋

⟦_⟧ₐ : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ₐctxt ML.⊢ ⟦ τ ⟧ₐty
⟦ var x ⟧ₐ = ML.var ⟦ x ⟧ₐ∋
⟦ nat n ⟧ₐ = ML.return (ML.nat n)
⟦ unit ⟧ₐ = ML.unit
