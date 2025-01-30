{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_)
open import Data.List using (List; []; _∷_)
open import categories
open import language-syntax

module language-interpretation {o m e}
  (𝒞 : Category o m e)
  (T  : HasTerminal 𝒞)
  (P  : HasProducts 𝒞)
  (B  : HasBooleans 𝒞 T P)
  (L  : HasLists 𝒞 T P)
  where

open Category 𝒞
open HasTerminal T renaming (witness to terminal)
open HasProducts P renaming (pair to ⟨_,_⟩)
open HasBooleans B
open HasLists L renaming (list to ⟦list⟧; nil to ⟦nil⟧; cons to ⟦cons⟧; fold to ⟦fold⟧)

list→product : ∀ {ℓ} {A : Set ℓ} → (A → obj) → List A → obj
list→product i [] = terminal
list→product i (x ∷ xs) = prod (i x) (list→product i xs)

record SignatureInterp {ℓ} (Sig : Signature ℓ) : Set (ℓ ⊔ o ⊔ m) where
  open Signature Sig
  field
    ⟦sort⟧ : sort → obj
    ⟦op⟧   : ∀ {i o} → op i o → list→product ⟦sort⟧ i ⇒ ⟦sort⟧ o
    ⟦rel⟧  : ∀ {i} → rel i → list→product ⟦sort⟧ i ⇒ Bool

module interp {ℓ} (Sig : Signature ℓ) (Int : SignatureInterp Sig) where

  open language Sig
  open SignatureInterp Int

  ⟦_⟧ty : type → obj
  ⟦ unit ⟧ty = terminal
  ⟦ bool ⟧ty = Bool
  ⟦ base σ ⟧ty = ⟦sort⟧ σ
  ⟦ τ₁ [×] τ₂ ⟧ty = prod ⟦ τ₁ ⟧ty ⟦ τ₂ ⟧ty
  ⟦ list τ ⟧ty = ⟦list⟧ ⟦ τ ⟧ty

  ⟦_⟧ctxt : ctxt → obj
  ⟦ emp ⟧ctxt = terminal
  ⟦ Γ , τ ⟧ctxt = prod ⟦ Γ ⟧ctxt ⟦ τ ⟧ty

  ⟦_⟧var : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
  ⟦ zero ⟧var = p₂
  ⟦ succ x ⟧var = ⟦ x ⟧var ∘ p₁

  mutual
    ⟦_⟧tm : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
    ⟦ var x ⟧tm = ⟦ x ⟧var
    ⟦ unit ⟧tm = terminal-mor _
    ⟦ true ⟧tm = True ∘ terminal-mor _
    ⟦ false ⟧tm = False ∘ terminal-mor _
    ⟦ if M then M₁ else M₂ ⟧tm = cond ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
    ⟦ pair M N ⟧tm = ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
    ⟦ fst M ⟧tm = p₁ ∘ ⟦ M ⟧tm
    ⟦ snd M ⟧tm = p₂ ∘ ⟦ M ⟧tm
    ⟦ bop ω Ms ⟧tm = ⟦op⟧ ω ∘ ⟦ Ms ⟧tms
    ⟦ brel ω Ms ⟧tm = ⟦rel⟧ ω ∘ ⟦ Ms ⟧tms
    ⟦ nil ⟧tm = ⟦nil⟧ ∘ terminal-mor _
    ⟦ cons M N ⟧tm = ⟦cons⟧ ∘ ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
    ⟦ fold M₁ M₂ M ⟧tm = ⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm ∘ ⟨ id _ , ⟦ M ⟧tm ⟩

    ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ list→product ⟦sort⟧ σs
    ⟦ [] ⟧tms = terminal-mor _
    ⟦ M ∷ Ms ⟧tms = ⟨ ⟦ M ⟧tm , ⟦ Ms ⟧tms ⟩
