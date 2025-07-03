{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ; suc; _⊔_)
open import Data.List using (List; []; _∷_)
open import signature using (Signature)
open import every using (Every; []; _∷_)

module language-syntax {ℓ} (Sig : Signature ℓ) where

open Signature Sig

data type : Set ℓ where
  unit bool : type
  base : sort → type
  _[×]_ _[→]_ : type → type → type
--    list : type → type

data first-order : type → Set ℓ where
  unit  : first-order unit
  bool  : first-order bool
  base  : ∀ s → first-order (base s)
  _[×]_ : ∀ {τ₁ τ₂} → first-order τ₁ → first-order τ₂ → first-order (τ₁ [×] τ₂)

infixl 40 _[×]_ _[→]_

data ctxt : Set ℓ where
  emp : ctxt
  _,_ : ctxt → type → ctxt

data first-order-ctxt : ctxt → Set ℓ where
  emp : first-order-ctxt emp
  _,_ : ∀ {Γ τ} → first-order-ctxt Γ → first-order τ → first-order-ctxt (Γ , τ)

infixl 30 _,_

data _∋_ : ctxt → type → Set ℓ where
  zero : ∀ {Γ τ} → (Γ , τ) ∋ τ
  succ : ∀ {Γ τ τ'} → Γ ∋ τ → Γ , τ' ∋ τ

-- A renaming is a context morphism
Ren : ctxt → ctxt → Set ℓ
Ren Γ Γ' = ∀ {τ} → Γ ∋ τ → Γ' ∋ τ

-- Push a renaming under a context extension.
ext : ∀ {Γ Γ' τ} → Ren Γ Γ' → Ren (Γ , τ) (Γ' , τ)
ext ρ zero = zero
ext ρ (succ x) = succ (ρ x)

weaken : ∀ {Γ τ} → Ren Γ (Γ , τ)
weaken zero = succ zero
weaken (succ x) = succ (weaken x)

data _⊢_ : ctxt → type → Set ℓ where
  var : ∀ {Γ τ} → Γ ∋ τ → Γ ⊢ τ

  unit : ∀ {Γ} → Γ ⊢ unit

  -- booleans
  true false : ∀ {Γ} → Γ ⊢ bool
  if_then_else_ : ∀ {Γ τ} → Γ ⊢ bool → Γ ⊢ τ → Γ ⊢ τ → Γ ⊢ τ

  -- products
  pair : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ → Γ ⊢ τ₂ → Γ ⊢ τ₁ [×] τ₂
  fst  : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ [×] τ₂ → Γ ⊢ τ₁
  snd  : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ [×] τ₂ → Γ ⊢ τ₂

  -- functions
  lam  : ∀ {Γ τ₁ τ₂} → Γ , τ₁ ⊢ τ₂ → Γ ⊢ τ₁ [→] τ₂
  app  : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ [→] τ₂ → Γ ⊢ τ₁ → Γ ⊢ τ₂

  -- base operations
  bop : ∀ {Γ in-sorts out-sort} →
        op in-sorts out-sort →
        Every (λ σ → Γ ⊢ base σ) in-sorts →
        Γ ⊢ base out-sort
  brel : ∀ {Γ in-sorts} →
         rel in-sorts →
         Every (λ σ → Γ ⊢ base σ) in-sorts →
         Γ ⊢ bool
{-
  -- lists; FIXME; reinstate
  nil  : ∀ {Γ τ} → Γ ⊢ list τ
  cons : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ list τ → Γ ⊢ list τ
  fold : ∀ {Γ τ₁ τ₂} →
         Γ ⊢ τ₂ →
         Γ , τ₁ , τ₂ ⊢ τ₂ →
         Γ ⊢ list τ₁ →
         Γ ⊢ τ₂
-}
-- Applying renamings to terms
mutual
  _*_ : ∀ {Γ Γ' τ} → Ren Γ Γ' → Γ ⊢ τ → Γ' ⊢ τ
  ρ * var x = var (ρ x)
  ρ * unit = unit
  ρ * true = true
  ρ * false = false
  ρ * (if M then M₁ else M₂) = if (ρ * M) then (ρ * M₁) else (ρ * M₂)
  ρ * pair M N = pair (ρ * M) (ρ * N)
  ρ * fst M = fst (ρ * M)
  ρ * snd M = snd (ρ * M)
  ρ * bop ω Ms = bop ω (ρ ** Ms)
  ρ * brel ω Ms = brel ω (ρ ** Ms)
  ρ * lam M = lam (ext ρ * M)
  ρ * app M N = app (ρ * M) (ρ * N)
  -- ρ * nil = nil
  -- ρ * cons M N = cons (ρ * M) (ρ * N)
  -- ρ * fold M₁ M₂ M = fold (ρ * M₁) (ext (ext ρ) * M₂) (ρ * M)

  _**_ : ∀ {Γ Γ' σs} → Ren Γ Γ' → Every (λ σ → Γ ⊢ base σ) σs → Every (λ σ → Γ' ⊢ base σ) σs
  ρ ** [] = []
  ρ ** (M ∷ Ms) = (ρ * M) ∷ (ρ ** Ms)

{-
-- “macros”
append : ∀ {Γ τ} → Γ ⊢ list τ → Γ ⊢ list τ → Γ ⊢ list τ
append xs ys = fold ys (cons (var (succ zero)) (var zero)) xs

return : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ list τ
return x = cons x nil

from_collect_ : ∀ {Γ τ₁ τ₂} → Γ ⊢ list τ₁ → Γ , τ₁ ⊢ list τ₂ → Γ ⊢ list τ₂
from M collect N = fold nil (append (weaken * N) (var zero)) M

when_；_ : ∀ {Γ τ} → Γ ⊢ bool → Γ ⊢ list τ → Γ ⊢ list τ
when M ； N = if M then N else nil
-}
