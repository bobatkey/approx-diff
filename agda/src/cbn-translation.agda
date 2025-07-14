{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.List using (List; []; _∷_)
open import signature using (Signature)
open import every
import language-syntax

module cbn-translation {ℓ} (Sig : Signature ℓ) (M : language-syntax.SynMonad Sig) where

open Signature Sig using (sort)
open language-syntax Sig
open SynMonad M

⟪_⟫ty : type → type
⟪ unit ⟫ty = unit
⟪ bool ⟫ty = bool
⟪ base s ⟫ty = base s
⟪ τ₁ [×] τ₂ ⟫ty = Mon ⟪ τ₁ ⟫ty [×] Mon ⟪ τ₂ ⟫ty
⟪ τ₁ [+] τ₂ ⟫ty = Mon ⟪ τ₁ ⟫ty [+] Mon ⟪ τ₂ ⟫ty
⟪ τ₁ [→] τ₂ ⟫ty = (Mon ⟪ τ₁ ⟫ty) [→] (Mon ⟪ τ₂ ⟫ty)
⟪ list τ ⟫ty = list (Mon ⟪ τ ⟫ty)

⟪_⟫ctxt : ctxt → ctxt
⟪ emp ⟫ctxt = emp
⟪ Γ , τ ⟫ctxt = ⟪ Γ ⟫ctxt , Mon ⟪ τ ⟫ty

⟪_⟫var : ∀ {Γ τ} → Γ ∋ τ → ⟪ Γ ⟫ctxt ∋ Mon ⟪ τ ⟫ty
⟪ zero ⟫var = zero
⟪ succ x ⟫var = succ ⟪ x ⟫var

_$_ : ∀ {Γ σ τ} → Γ ⊢ σ [→] τ → Γ ⊢ σ → Γ ⊢ τ
_$_ = app

infixl 10 _$_

mutual
  ⟪_⟫tm : ∀ {Γ τ} → Γ ⊢ τ → ⟪ Γ ⟫ctxt ⊢ Mon ⟪ τ ⟫ty
  ⟪ var x ⟫tm = var ⟪ x ⟫var
  ⟪ unit ⟫tm = pure $ unit
  ⟪ true ⟫tm = pure $ true
  ⟪ false ⟫tm = pure $ false
  ⟪ if M then M₁ else M₂ ⟫tm =
    bind $ ⟪ M ⟫tm $ lam (if (var zero) then (weaken * ⟪ M₁ ⟫tm) else (weaken * ⟪ M₂ ⟫tm))
  ⟪ inl M ⟫tm = pure $ inl ⟪ M ⟫tm
  ⟪ inr M ⟫tm = pure $ inr ⟪ M ⟫tm
  ⟪ case M N₁ N₂ ⟫tm = bind $ ⟪ M ⟫tm $ lam (case (var zero) (ext weaken * ⟪ N₁ ⟫tm) (ext weaken * ⟪ N₂ ⟫tm))
  ⟪ pair M₁ M₂ ⟫tm = pure $ pair ⟪ M₁ ⟫tm ⟪ M₂ ⟫tm
  ⟪ fst M ⟫tm = bind $ ⟪ M ⟫tm $ lam (fst (var zero))
  ⟪ snd M ⟫tm = bind $ ⟪ M ⟫tm $ lam (snd (var zero))
  ⟪ lam M ⟫tm = pure $ lam ⟪ M ⟫tm
  ⟪ app M₁ M₂ ⟫tm = bind $ ⟪ M₁ ⟫tm $ lam ((var zero) $ (weaken * ⟪ M₂ ⟫tm))
  ⟪ bop ω Ms ⟫tm = bindAll Ms (id-ren _) λ ρ Ms' → pure $ bop ω Ms'
  ⟪ brel r Ms ⟫tm = bindAll Ms (id-ren _) λ ρ Ms' → pure $ brel r Ms'
  ⟪ nil ⟫tm = pure $ nil
  ⟪ cons M N ⟫tm = bind $ ⟪ N ⟫tm $ lam (pure $ cons (weaken * ⟪ M ⟫tm) (var zero))
  ⟪ fold M N L ⟫tm =
    bind $ ⟪ L ⟫tm $ lam (fold (weaken * ⟪ M ⟫tm) (ext (ext weaken) * ⟪ N ⟫tm) (var zero))

  bindAll : ∀ {Γ Γ' σs τ} →
            Every (λ σ → Γ ⊢ base σ) σs →
            Ren ⟪ Γ ⟫ctxt Γ' →
            (∀ {Γ''} → Ren Γ' Γ'' → Every (λ σ → Γ'' ⊢ base σ) σs → Γ'' ⊢ Mon τ) →
            Γ' ⊢ Mon τ
  bindAll [] ρ κ = κ (id-ren _) []
  bindAll (M ∷ Ms) ρ κ =
    bind $ (ρ * ⟪ M ⟫tm) $ lam (bindAll Ms (weaken ∘ren ρ) λ ρ' Ms' → κ (λ x → ρ' (succ x)) (var (ρ' zero) ∷ Ms'))
