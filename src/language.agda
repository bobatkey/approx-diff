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

  -- Natural numbers and some operations
  nat : ∀ {Γ} → ℕ → Γ ⊢ num
  plus : ∀ {Γ} → Γ ⊢ num → Γ ⊢ num → Γ ⊢ num

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

open import Data.Product using (_×_; _,_)
open import reverse
open _⇒_

⟦_⟧ty : type → ApproxSet
⟦ unit ⟧ty = ⊤ₐ
⟦ num ⟧ty = Disc ℕ
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

binOp : (ℕ → ℕ → ℕ) → (Disc ℕ ⊗ Disc ℕ) ⇒ Disc ℕ
binOp f = (Disc-f λ (x , y) → f x y) ∘ Disc-reflects-products

⟦_⟧ : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
⟦ var x ⟧ = ⟦ x ⟧var
⟦ unit ⟧ = terminal
⟦ nat n ⟧ = Disc-const n ∘ terminal
⟦ plus s t ⟧ = binOp Data.Nat._+_ ∘ pair ⟦ s ⟧ ⟦ t ⟧
⟦ lam t ⟧ = lambda ⟦ t ⟧
⟦ app s t ⟧ = eval ∘ pair ⟦ s ⟧ ⟦ t ⟧
⟦ fst t ⟧ = π₁ ∘ ⟦ t ⟧
⟦ snd t ⟧ = π₂ ∘ ⟦ t ⟧
⟦ mkPair s t ⟧ = pair ⟦ s ⟧ ⟦ t ⟧
⟦ inj₁ t ⟧ = inl ∘ ⟦ t ⟧
⟦ inj₂ t ⟧ = inr ∘ ⟦ t ⟧
⟦ case t₁ t₂ s ⟧ = [ ⟦ t₁ ⟧ , ⟦ t₂ ⟧ ] ∘ pair id ⟦ s ⟧
⟦ return t ⟧ = ℒ-unit ∘ ⟦ t ⟧
⟦ bind s t ⟧ = ((ℒ-join ∘ ℒ-func ⟦ t ⟧) ∘ ℒ-strength) ∘ pair id ⟦ s ⟧

-- A renaming is a context morphism
Ren : ctxt → ctxt → Set
Ren Γ Γ' = ∀ {τ} → Γ ∋ τ → Γ' ∋ τ

-- Push a renaming under a context extension.
ext : ∀ {Γ Γ' τ} → Ren Γ Γ' → Ren (Γ -, τ) (Γ' -, τ)
ext ρ ze = ze
ext ρ (su x) = su (ρ x)

weaken : ∀ {Γ τ} → Ren Γ (Γ -, τ)
weaken ze = su ze
weaken (su x) = su (weaken x)

_*_ : ∀ {Γ Γ' τ} → Ren Γ Γ' → Γ ⊢ τ → Γ' ⊢ τ
ρ * var x = var (ρ x)
ρ * nat n = nat n
ρ * plus s t = plus (ρ * s) (ρ * t)
ρ * unit = unit
ρ * lam t = lam (ext ρ * t)
ρ * app s t = app (ρ * s) (ρ * t)
ρ * fst t = fst (ρ * t)
ρ * snd t = snd (ρ * t)
ρ * mkPair s t = mkPair (ρ * s) (ρ * t)
ρ * inj₁ t = inj₁ (ρ * t)
ρ * inj₂ t = inj₂ (ρ * t)
ρ * case t₁ t₂ s = case (ext ρ * t₁) (ext ρ * t₂) (ρ * s)
ρ * return t = return (ρ * t)
ρ * bind s t = bind (ρ * s) (ext ρ * t)
