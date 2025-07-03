{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_)
open import Data.List using (List; []; _∷_)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasExponentials; HasBooleans; coproducts+exp→booleans)
import language-syntax
open import signature using (Signature; Model; PFPC[_,_,_,_]; PointedFPCat)
open import every using (Every; []; _∷_)

module language-interpretation
  {ℓ} (Sig : Signature ℓ)
  {o m e}
  (𝒞 : Category o m e)
  (T  : HasTerminal 𝒞)
  (P  : HasProducts 𝒞)
  (C  : HasCoproducts 𝒞)
  (E  : HasExponentials 𝒞 P)
  (Int : Model PFPC[ 𝒞 , T , P , HasBooleans.Bool (coproducts+exp→booleans T C E) ] Sig)
--  (L  : HasLists 𝒞 T P)
  where

B : HasBooleans 𝒞 T P
B = coproducts+exp→booleans T C E

open HasExponentials E renaming (exp to _⟦→⟧_)
open PointedFPCat PFPC[ 𝒞 , T , P , HasBooleans.Bool B ]
open HasBooleans B
-- open HasLists L renaming (list to ⟦list⟧; nil to ⟦nil⟧; cons to ⟦cons⟧; fold to ⟦fold⟧)

open language-syntax Sig
open Model Int

⟦_⟧ty : type → obj
⟦ unit ⟧ty = 𝟙
⟦ bool ⟧ty = Bool
⟦ base σ ⟧ty = ⟦sort⟧ σ
⟦ τ₁ [×] τ₂ ⟧ty = ⟦ τ₁ ⟧ty × ⟦ τ₂ ⟧ty
⟦ τ₁ [→] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⟦→⟧ ⟦ τ₂ ⟧ty

-- ⟦ list τ ⟧ty = ⟦list⟧ ⟦ τ ⟧ty

⟦_⟧ctxt : ctxt → obj
⟦ emp ⟧ctxt = 𝟙
⟦ Γ , τ ⟧ctxt = ⟦ Γ ⟧ctxt × ⟦ τ ⟧ty

⟦_⟧var : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
⟦ zero ⟧var = p₂
⟦ succ x ⟧var = ⟦ x ⟧var ∘ p₁

mutual
  ⟦_⟧tm : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
  ⟦ var x ⟧tm = ⟦ x ⟧var
  ⟦ unit ⟧tm = to-terminal
  ⟦ true ⟧tm = True ∘ to-terminal
  ⟦ false ⟧tm = False ∘ to-terminal
  ⟦ if M then M₁ else M₂ ⟧tm = cond ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
  ⟦ pair M N ⟧tm = ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ fst M ⟧tm = p₁ ∘ ⟦ M ⟧tm
  ⟦ snd M ⟧tm = p₂ ∘ ⟦ M ⟧tm
  ⟦ lam M ⟧tm = lambda ⟦ M ⟧tm
  ⟦ app M  N ⟧tm = eval ∘ ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ bop ω Ms ⟧tm = ⟦op⟧ ω ∘ ⟦ Ms ⟧tms
  ⟦ brel ω Ms ⟧tm = ⟦rel⟧ ω ∘ ⟦ Ms ⟧tms
  -- ⟦ nil ⟧tm = ⟦nil⟧ ∘ is-terminal .to-terminal
  -- ⟦ cons M N ⟧tm = ⟦cons⟧ ∘ ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  -- ⟦ fold M₁ M₂ M ⟧tm = ⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm ∘ ⟨ id _ , ⟦ M ⟧tm ⟩

  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ list→product ⟦sort⟧ σs
  ⟦ [] ⟧tms = to-terminal
  ⟦ M ∷ Ms ⟧tms = ⟨ ⟦ M ⟧tm , ⟦ Ms ⟧tms ⟩
