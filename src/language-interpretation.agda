{-# OPTIONS --prop --postfix-projections #-}

open import categories
open import language-syntax

module language-interpretation {o m e}
  (𝒞 : Category o m e)
  (T  : HasTerminal 𝒞)
  (P  : HasProducts 𝒞)
  (S  : HasStrongCoproducts 𝒞 P)
  (E  : HasExponentials 𝒞 P)
  (L  : StrongMonad 𝒞 P)
  where

open Category 𝒞
open HasTerminal T renaming (witness to terminal)
open HasProducts P
open HasStrongCoproducts S
open HasExponentials E
open StrongMonad L renaming (M to Lobj; unit to Lunit)

⟦_⟧ty : type → obj
⟦ unit ⟧ty = terminal
⟦ num ⟧ty = {!!}
⟦ σ `× τ ⟧ty = prod ⟦ σ ⟧ty ⟦ τ ⟧ty
⟦ σ `⇒ τ ⟧ty = exp ⟦ σ ⟧ty ⟦ τ ⟧ty
⟦ σ `+ τ ⟧ty = coprod ⟦ σ ⟧ty ⟦ τ ⟧ty
⟦ lift τ ⟧ty = Lobj ⟦ τ ⟧ty

⟦_⟧ctxt : ctxt → obj
⟦ ε ⟧ctxt     = terminal
⟦ Γ , τ ⟧ctxt = prod ⟦ Γ ⟧ctxt ⟦ τ ⟧ty

⟦_⟧var : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
⟦ zero ⟧var = p₂
⟦ su x ⟧var = ⟦ x ⟧var ∘ p₁

⟦_⟧tm : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
⟦ var x ⟧tm = ⟦ x ⟧var
⟦ unit ⟧tm = terminal-mor _
⟦ nat n ⟧tm = {!!}
⟦ plus M N ⟧tm = {!!}
⟦ times M N ⟧tm = {!!}
⟦ eq M N ⟧tm = {!!}
⟦ lam M ⟧tm = lambda ⟦ M ⟧tm
⟦ app M N ⟧tm = eval ∘ pair ⟦ N ⟧tm ⟦ M ⟧tm
⟦ fst M ⟧tm = p₁ ∘ ⟦ M ⟧tm
⟦ snd M ⟧tm = p₂ ∘ ⟦ M ⟧tm
⟦ mkPair M N ⟧tm = pair ⟦ M ⟧tm ⟦ N ⟧tm
⟦ inj₁ M ⟧tm = in₁ ∘ ⟦ M ⟧tm
⟦ inj₂ M ⟧tm = in₂ ∘ ⟦ M ⟧tm
⟦ case M₁ M₂ N ⟧tm = copair ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm ∘ (pair (id _) ⟦ N ⟧tm)
⟦ return M ⟧tm = Lunit ∘ ⟦ M ⟧tm
⟦ bind M N ⟧tm = extend ⟦ N ⟧tm ∘ (pair (id _) ⟦ M ⟧tm)
