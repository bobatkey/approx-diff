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

open import language renaming (
  type to typeₘₗ; ctxt to ctxtₘₗ; _∋_ to _∋ₘₗ_; _⊢_ to _⊢ₘₗ_;
  ε to εₘₗ; _-,_ to _-,ₘₗ_; ze to zeₘₗ; su to suₘₗ;
  unit to unitₘₗ; num to numₘₗ; _`×_ to _`×ₘₗ_; _`⇒_ to _`⇒ₘₗ_; _`+_ to _`+ₘₗ_; lift to liftₘₗ;
  var to varₘₗ; nat to natₘₗ; lam to lamₘₗ; app to appₘₗ;
  fst to fstₘₗ; snd to sndₘₗ; mkPair to mkPairₘₗ; inj₁ to inj₁ₘₗ; inj₂ to inj₂ₘₗ; case to caseₘₗ
  )

⟦_⟧ₐty : type → typeₘₗ
⟦ unit ⟧ₐty = unitₘₗ
⟦ num ⟧ₐty = numₘₗ
⟦ σ `× τ ⟧ₐty = liftₘₗ ⟦ σ ⟧ₐty `×ₘₗ liftₘₗ ⟦ τ ⟧ₐty
⟦ σ `⇒ τ ⟧ₐty = liftₘₗ ⟦ σ ⟧ₐty `⇒ₘₗ liftₘₗ ⟦ τ ⟧ₐty
⟦ σ `+ τ ⟧ₐty = liftₘₗ ⟦ σ ⟧ₐty `+ₘₗ liftₘₗ ⟦ τ ⟧ₐty

⟦_⟧ₐctxt : ctxt → ctxtₘₗ
⟦ ε ⟧ₐctxt = εₘₗ
⟦ Γ -, τ ⟧ₐctxt = ⟦ Γ ⟧ₐctxt -,ₘₗ liftₘₗ ⟦ τ ⟧ₐty

⟦_⟧ₐ∋ : ∀ {Γ σ} → Γ ∋ σ → ⟦ Γ ⟧ₐctxt ∋ₘₗ liftₘₗ ⟦ σ ⟧ₐty
⟦ ze ⟧ₐ∋ = zeₘₗ
⟦ su x ⟧ₐ∋ = suₘₗ ⟦ x ⟧ₐ∋

⟦_⟧ₐ : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ₐctxt ⊢ₘₗ liftₘₗ ⟦ τ ⟧ₐty
⟦ var x ⟧ₐ = varₘₗ ⟦ x ⟧ₐ∋
⟦ unit ⟧ₐ = return unitₘₗ
⟦ nat n ⟧ₐ = return (natₘₗ n)
⟦ lam t ⟧ₐ = return (lamₘₗ ⟦ t ⟧ₐ)
⟦ app s t ⟧ₐ = bind ⟦ s ⟧ₐ (appₘₗ (varₘₗ zeₘₗ) (weaken * ⟦ t ⟧ₐ))
⟦ fst t ⟧ₐ = bind ⟦ t ⟧ₐ (fstₘₗ (varₘₗ zeₘₗ))
⟦ snd t ⟧ₐ = bind ⟦ t ⟧ₐ (sndₘₗ (varₘₗ zeₘₗ))
⟦ mkPair s t ⟧ₐ = return (mkPairₘₗ ⟦ s ⟧ₐ ⟦ t ⟧ₐ)
⟦ inj₁ t ⟧ₐ = return (inj₁ₘₗ ⟦ t ⟧ₐ)
⟦ inj₂ t ⟧ₐ = return (inj₂ₘₗ ⟦ t ⟧ₐ)
⟦ case t₁ t₂ s ⟧ₐ = bind ⟦ s ⟧ₐ (caseₘₗ (ext weaken * ⟦ t₁ ⟧ₐ) (ext weaken * ⟦ t₂ ⟧ₐ) (varₘₗ zeₘₗ))
