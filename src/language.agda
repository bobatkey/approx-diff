{-# OPTIONS --postfix-projections --without-K --safe #-}

module language where

open import Data.Nat using (ℕ)

data type : Set where
  unit num : type
  _`×_ _`⇒_ _`+_ : type → type → type
  lift : type → type

infix 4 _∋_ _⊢_

data ctxt : Set where
  ε : ctxt
  _-,_ : ctxt → type → ctxt

data _∋_ : ctxt → type → Set where
  ze : ∀ {Γ τ} → Γ -, τ ∋ τ
  su : ∀ {Γ τ σ} → Γ ∋ τ → Γ -, σ ∋ τ

data _⊢_ : ctxt → type → Set where
  var : ∀ {Γ τ} → Γ ∋ τ → Γ ⊢ τ

  -- Natural numbers and some operations.
  nat : ∀ {Γ} → ℕ -> Γ ⊢ num
  plus : ∀ {Γ} → Γ ⊢ num -> Γ ⊢ num -> Γ ⊢ num

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

  -- lift
  return : ∀ {Γ τ} → Γ ⊢ τ →
                     Γ ⊢ lift τ
  bind   : ∀ {Γ σ τ} → Γ ⊢ lift σ →
                       Γ -, σ ⊢ lift τ →
                       Γ ⊢ lift τ
{-
  -- lists
  nil  : ∀ {Γ τ} → Γ ⊢ list τ
  cons : ∀ {Γ τ} → Γ ⊢ lift (τ `× list τ) →
                   Γ ⊢ list τ
  rec  : ∀ {Γ σ τ} → Γ ⊢ σ →
                     Γ -, lift (τ `× σ) ⊢ σ →
                     Γ ⊢ list τ →
                     Γ ⊢ σ
-}

open import Data.Product using (_,_)
open import reverse
open import primops
open _⇒_

⟦_⟧ty : type → ApproxSet
⟦ unit ⟧ty = ⊤ₐ
⟦ num ⟧ty = ℒ (Disc ℕ)
⟦ σ `× τ ⟧ty = ⟦ σ ⟧ty ⊗ ⟦ τ ⟧ty
⟦ σ `⇒ τ ⟧ty = ⟦ σ ⟧ty ⊸ ⟦ τ ⟧ty
⟦ σ `+ τ ⟧ty = ⟦ σ ⟧ty + ⟦ τ ⟧ty
⟦ lift τ ⟧ty = ℒ ⟦ τ ⟧ty

⟦_⟧ctxt : ctxt → ApproxSet
⟦ ε ⟧ctxt      = ⊤ₐ
⟦ Γ -, τ ⟧ctxt = ⟦ Γ ⟧ctxt ⊗ ⟦ τ ⟧ty

⟦_⟧var : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
⟦ ze ⟧var = π₂
⟦ su x ⟧var = ⟦ x ⟧var ∘ π₁

eval-plus : ⟦ num `× num ⟧ty ⇒ ⟦ num ⟧ty
eval-plus .func (n , m) = Data.Nat._+_ n m
eval-plus .fwd (n , m) = plus-fwd
eval-plus .bwd (n , m) = plus-bwd

⟦_⟧ : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
⟦ var x ⟧ = ⟦ x ⟧var
⟦ unit ⟧ = terminal
⟦ nat n ⟧ = (ℒ-unit ∘ Disc-const n) ∘ terminal
⟦ plus s t ⟧ = eval-plus ∘ pair ⟦ s ⟧ ⟦ t ⟧
⟦ lam t ⟧ = lambda ⟦ t ⟧
⟦ app s t ⟧ = eval ∘ pair ⟦ s ⟧ ⟦ t ⟧
⟦ fst t ⟧ = π₁ ∘ ⟦ t ⟧
⟦ snd t ⟧ = π₂ ∘ ⟦ t ⟧
⟦ mkPair s t ⟧ = pair ⟦ s ⟧ ⟦ t ⟧
⟦ inj₁ t ⟧ = inl ∘ ⟦ t ⟧
⟦ inj₂ t ⟧ = inr ∘ ⟦ t ⟧
⟦ _⊢_.case t₁ t₂ s ⟧ = reverse.case ⟦ t₁ ⟧ ⟦ t₂ ⟧ ∘ pair id ⟦ s ⟧
⟦ return t ⟧ = ℒ-unit ∘ ⟦ t ⟧
⟦ bind s t ⟧ = ((ℒ-join ∘ ℒ-func ⟦ t ⟧) ∘ ℒ-strength) ∘ pair id ⟦ s ⟧
