{-# OPTIONS --postfix-projections --without-K --safe #-}

module surface-language where

open import Data.Nat using (ℕ)

data type : Set where
  unit num : type
  _`×_ _`⇒_ _`+_ : type → type → type

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

  -- lambda and application
  lam : ∀ {Γ σ τ} → Γ -, σ ⊢ τ → Γ ⊢ σ `⇒ τ
  app : ∀ {Γ σ τ} → Γ ⊢ σ `⇒ τ → Γ ⊢ σ → Γ ⊢ τ

  -- pairs
  fst    : ∀ {Γ σ τ} → Γ ⊢ σ `× τ → Γ ⊢ σ
  snd    : ∀ {Γ σ τ} → Γ ⊢ σ `× τ → Γ ⊢ τ
  mkPair : ∀ {Γ σ τ} → Γ ⊢ σ → Γ ⊢ τ → Γ ⊢ σ `× τ

  -- sums
  inj₁ : ∀ {Γ σ τ} → Γ ⊢ σ → Γ ⊢ σ `+ τ
  inj₂ : ∀ {Γ σ τ} → Γ ⊢ τ → Γ ⊢ σ `+ τ
  case : ∀ {Γ ρ σ τ} → Γ -, σ ⊢ ρ → Γ -, τ ⊢ ρ → Γ ⊢ σ `+ τ → Γ ⊢ ρ

-- A renaming is a context morphism
Ren : ctxt → ctxt → Set
Ren Γ Γ' = ∀ {τ} -> Γ ∋ τ → Γ' ∋ τ

-- Extend a renaming with an identity maplet.
ext : ∀ {Γ Γ' τ} → Ren Γ Γ' → Ren (Γ -, τ) (Γ' -, τ)
ext ρ ze = ze
ext ρ (su x) = su (ρ x)

weaken : ∀ {Γ τ} → Ren Γ (Γ -, τ)
weaken {Γ} {τ} ze = su ze
weaken (su x) = su (weaken x)

_*_ : ∀ {Γ Γ' τ} -> Ren Γ Γ' → Γ ⊢ τ → Γ' ⊢ τ
ρ * var x = var (ρ x)
ρ * nat n = nat n
ρ * unit = unit
ρ * (lam t) = lam (ext ρ * t)
ρ * app s t = app (ρ * s) (ρ * t)
ρ * fst t = fst (ρ * t)
ρ * snd t = snd (ρ * t)
ρ * mkPair s t = mkPair (ρ * s) (ρ * t)
ρ * inj₁ t = inj₁ (ρ * t)
ρ * inj₂ t = inj₂ (ρ * t)
ρ * (case t₁ t₂ s) = case (ext ρ * t₁) (ext ρ * t₂) (ρ * s)

import language as ML

⟦_⟧ₐty : type → ML.type
⟦ unit ⟧ₐty = ML.unit
⟦ num ⟧ₐty = ML.num
⟦ σ `× τ ⟧ₐty = ML.lift ⟦ σ ⟧ₐty ML.`× ML.lift ⟦ τ ⟧ₐty
⟦ σ `⇒ τ ⟧ₐty = ML.lift ⟦ σ ⟧ₐty ML.`⇒ ML.lift ⟦ τ ⟧ₐty
⟦ σ `+ τ ⟧ₐty = ML.lift ⟦ σ ⟧ₐty ML.`+ ML.lift ⟦ τ ⟧ₐty

⟦_⟧ₐctxt : ctxt → ML.ctxt
⟦ ε ⟧ₐctxt      = ML.ε
⟦ Γ -, τ ⟧ₐctxt = ⟦ Γ ⟧ₐctxt ML.-, ML.lift ⟦ τ ⟧ₐty

⟦_⟧ₐ∋ : ∀ {Γ σ} → Γ ∋ σ → ⟦ Γ ⟧ₐctxt ML.∋ ML.lift ⟦ σ ⟧ₐty
⟦ ze ⟧ₐ∋ = ML.ze
⟦ su x ⟧ₐ∋ = ML.su ⟦ x ⟧ₐ∋

⟦_⟧ₐ : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ₐctxt ML.⊢ ML.lift ⟦ τ ⟧ₐty
⟦ var x ⟧ₐ = ML.var ⟦ x ⟧ₐ∋
⟦ unit ⟧ₐ = ML.return ML.unit
⟦ nat n ⟧ₐ = ML.return (ML.nat n)
⟦ lam t ⟧ₐ = ML.return (ML.lam ⟦ t ⟧ₐ)
⟦ app s t ⟧ₐ = ML.bind ⟦ s ⟧ₐ (ML.app (ML.var ML.ze) {!   !})
⟦ fst t ⟧ₐ = ML.bind ⟦ t ⟧ₐ (ML.fst (ML.var ML.ze))
⟦ snd t ⟧ₐ = ML.bind ⟦ t ⟧ₐ (ML.snd (ML.var ML.ze))
⟦ mkPair s t ⟧ₐ = ML.return (ML.mkPair ⟦ s ⟧ₐ ⟦ t ⟧ₐ)
⟦ inj₁ t ⟧ₐ = ML.return (ML.inj₁ ⟦ t ⟧ₐ)
⟦ inj₂ t ⟧ₐ = ML.return ((ML.inj₂ ⟦ t ⟧ₐ))
⟦ case t₁ t₂ s ⟧ₐ = ML.bind ⟦ s ⟧ₐ (ML.case {!   !} ({!   !}) (ML.var ML.ze))
