{-# OPTIONS --postfix-projections --without-K --safe #-}

module language where

open import Data.Nat using (ℕ; _≟_)

module Syntax where
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

    -- The sole value of the unit type
    unit : ∀ {Γ} → Γ ⊢ unit

    -- Natural numbers and some operations
    nat : ∀ {Γ} → ℕ → Γ ⊢ num
    plus : ∀ {Γ} → Γ ⊢ num → Γ ⊢ num → Γ ⊢ num
    times : ∀ {Γ} → Γ ⊢ num → Γ ⊢ num → Γ ⊢ num
    eq : ∀ {Γ} → Γ ⊢ num → Γ ⊢ num → Γ ⊢ unit `+ unit

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
  ρ * times s t = times (ρ * s) (ρ * t)
  ρ * eq s t = eq (ρ * s) (ρ * t)
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

module AsFOApproxSet where
  open Syntax
  open import Data.Product using (_×_; _,_)
  open import approxset
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
  ⟦ times s t ⟧ = binOp Data.Nat._*_ ∘ pair ⟦ s ⟧ ⟦ t ⟧
  ⟦ eq s t ⟧ = (binPred _≟_ ∘ Disc-reflects-products) ∘ pair ⟦ s ⟧ ⟦ t ⟧
  ⟦ lam t ⟧ = lambda ⟦ t ⟧
  ⟦ app s t ⟧ = eval ∘ pair ⟦ s ⟧ ⟦ t ⟧
  ⟦ fst t ⟧ = π₁ ∘ ⟦ t ⟧
  ⟦ snd t ⟧ = π₂ ∘ ⟦ t ⟧
  ⟦ mkPair s t ⟧ = pair ⟦ s ⟧ ⟦ t ⟧
  ⟦ inj₁ t ⟧ = inl ∘ ⟦ t ⟧
  ⟦ inj₂ t ⟧ = inr ∘ ⟦ t ⟧
  ⟦ case t₁ t₂ s ⟧ = [ ⟦ t₁ ⟧ , ⟦ t₂ ⟧ ] ∘ pair id ⟦ s ⟧
  ⟦ return t ⟧ = ℒ-unit ∘ ⟦ t ⟧
  ⟦ bind s t ⟧ = ((ℒ-join ∘ ℒ-map ⟦ t ⟧) ∘ ℒ-strength) ∘ pair id ⟦ s ⟧

module syntax' where
  open import Level

  -- syntax with universe level of its interpretation; kludge for now
  data type : Level -> Set where
    unit : type 0ℓ
    num : type 0ℓ
    _`×_ : ∀ {a b} (σ : type a) (τ : type b) → type (a ⊔ b)
    _`⇒_ : ∀ {a b} (σ : type a) (τ : type b) → type (suc (a ⊔ b))
    _`+_ : ∀ {a} (σ : type a) (τ : type a) → type a
    lift : ∀ {a} (τ : type a) → type a

  infix 4 _∋_ _⊢_

  data ctxt : Level -> Set where
    ε : ctxt 0ℓ
    _-,_ : ∀ {a b} (Γ : ctxt a) (τ : type b) → ctxt (a ⊔ b)

  data _∋_ : ∀ {a} (Γ : ctxt a) (τ : type a) → Set where
    ze : ∀ {a} {Γ : ctxt a} {τ : type a} → Γ -, τ ∋ τ
    su : ∀ {a} {Γ : ctxt a} {τ : type a} {σ : type a} → Γ ∋ τ → Γ -, σ ∋ τ

  data _⊢_ : ∀ {a b} → ctxt a → type b → Set where
    var : ∀ {a Γ} {τ : type a} → Γ ∋ τ → Γ ⊢ τ

    -- The sole value of the unit type
    unit : ∀ {a} {Γ : ctxt a} → Γ ⊢ unit

    -- Natural numbers and some operations
    nat : ∀ {a} {Γ : ctxt a} → ℕ → Γ ⊢ num
    plus : ∀ {a} {Γ : ctxt a} → Γ ⊢ num → Γ ⊢ num → Γ ⊢ num
    times : ∀ {a} {Γ : ctxt a} → Γ ⊢ num → Γ ⊢ num → Γ ⊢ num
    eq : ∀ {a} {Γ : ctxt a} → Γ ⊢ num → Γ ⊢ num → Γ ⊢ unit `+ unit

    -- lambda and application
    lam : ∀ {a b c} {Γ : ctxt a} {σ : type b} {τ : type c} → Γ -, σ ⊢ τ → Γ ⊢ σ `⇒ τ
    app : ∀ {a b c} {Γ : ctxt a} {σ : type b} {τ : type c} → Γ ⊢ σ `⇒ τ → Γ ⊢ σ → Γ ⊢ τ

    -- pairs
    fst : ∀ {a b c} {Γ : ctxt a} {σ : type b} {τ : type c} → Γ ⊢ σ `× τ → Γ ⊢ σ
    snd : ∀ {a b c} {Γ : ctxt a} {σ : type b} {τ : type c} → Γ ⊢ σ `× τ → Γ ⊢ τ
    mkPair : ∀ {a b c} {Γ : ctxt a} {σ : type b} {τ : type c} → Γ ⊢ σ → Γ ⊢ τ → Γ ⊢ σ `× τ

    -- sums
    inj₁ : ∀ {a b} {Γ : ctxt a} {σ : type b} {τ : type b} → Γ ⊢ σ → Γ ⊢ σ `+ τ
    inj₂ : ∀ {a b} {Γ : ctxt a} {σ : type b} {τ : type b} → Γ ⊢ τ → Γ ⊢ σ `+ τ
    case : ∀ {a b c} {Γ : ctxt a} {σ τ : type b} {σ' : type c} → Γ -, σ ⊢ σ' → Γ -, τ ⊢ σ' → Γ ⊢ σ `+ τ → Γ ⊢ σ'

    -- lift
    return : ∀ {a b} {Γ : ctxt a} {τ : type b} → Γ ⊢ τ → Γ ⊢ lift τ
    bind   : ∀ {a b c} {Γ : ctxt a} {σ : type b} {τ : type c} → Γ ⊢ lift σ → Γ -, σ ⊢ lift τ → Γ ⊢ lift τ

module AsFOApproxSetPSh where
  open import Level
  open import Data.Product using (Σ; _×_; _,_)
  open syntax'
  open import fo-approxset-presheaf
  open _⇒_

  module _ where
    open FOApproxSetPSh

    ⟦_⟧ty : ∀ {a} (τ : type a) → FOApproxSetPSh a
    ⟦ unit ⟧ty = ⊤
    ⟦ num ⟧ty = Disc ℕ
    ⟦ σ `× τ ⟧ty = ⟦ σ ⟧ty ⊗ ⟦ τ ⟧ty
    ⟦ σ `⇒ τ ⟧ty = ⟦ σ ⟧ty ⊸ ⟦ τ ⟧ty
    ⟦ σ `+ τ ⟧ty = ⟦ σ ⟧ty + ⟦ τ ⟧ty
    ⟦ lift τ ⟧ty = ℒ ⟦ τ ⟧ty

    ⟦_⟧ctxt : ∀ {a} (Γ : ctxt a) → FOApproxSetPSh a
    ⟦ ε ⟧ctxt = ⊤
    ⟦ Γ -, τ ⟧ctxt = ⟦ Γ ⟧ctxt ⊗ ⟦ τ ⟧ty

    ⟦_⟧var : ∀ {a} {Γ : ctxt a} {τ : type a} → Γ ∋ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
    ⟦ ze ⟧var = π₂
    ⟦ su x ⟧var = ⟦ x ⟧var ∘ π₁
