{-# OPTIONS --postfix-projections --prop --safe #-}

module conservativity where

open import Level
open import prop using (_,_; proj₁; proj₂; ∃)
open import categories using (Category; HasBooleans; HasProducts; HasCoproducts; HasExponentials; HasTerminal; IsTerminal; IsProduct; coproducts+exp→booleans)
open import functor using (Functor)
open import prop-setoid using (module ≈-Reasoning)
open import setoid-cat using (SetoidCat)
import sconing
import glueing-simple
import setoid-predicate

import language-syntax
import language-interpretation
open import signature

open Functor

-- Let Sig be a signature
-- Let M be a model of Sig in 𝒞, and F be a finite product and infinite coproduct preserving functor
-- Then:
--   1. Can interpret the whole language in Glued
--   2. Every first order type is isomorphic to its interpretation in 𝒞
--   3. So every judgement x : A ⊢ M : B, with A, B first-order, has a morphism g : A 𝒞.⇒ B such that F(g) = ⟦ M ⟧

-- For the actual language:
--  1. 𝒞 = Fam⟨LatGal⟩ which has finite products and infinite coproducts
--  2. 𝒟 = Fam⟨M×J^op⟩ which is a BiCCC
--  3. F  = Fam⟨𝓖⟩ which preserves products and infinite coproducts
-- Could also replay the whole thing with `Stable` instead of Fam⟨LatGal⟩ ??


module _ {ℓ} (Sig : Signature ℓ)
         {o m e}
         -- Category for interpreting first-order things
         (𝒞 : Category o m e) (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞)
         (Int : Model PFPC[ 𝒞 , 𝒞T , 𝒞P , {!!} ] Sig)
         -- A higher order model
         (𝒟 : Category o m e)
         (𝒟T : HasTerminal 𝒟) (𝒟P : HasProducts 𝒟) (𝒟CP : HasCoproducts 𝒟) (𝒟E : HasExponentials 𝒟 𝒟P)
         -- A functor which preserves finite products (and the boolean object)
         (F  : Functor 𝒞 𝒟) (FP : FPFunctor F)
  where

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟

  module L = language-syntax.language Sig

  module 𝒟Interp =
    language-interpretation
      Sig
      𝒟 𝒟T 𝒟P 𝒟E (coproducts+exp→booleans 𝒟T 𝒟CP 𝒟E)
      (transport-model Sig F FP {!!} Int)

  module glued (Env : Category.obj 𝒞) where

    module Sc = sconing 𝒟 𝒟P (F .fobj Env)
    open Sc using (Scone)

    module G = glueing-simple 𝒟 (SetoidCat m e) _ _ setoid-predicate.system Sc.Scone
    module GCP = G.coproducts 𝒟CP
    module GPE = G.products-and-exponentials 𝒟T 𝒟P 𝒟E Sc.mul Sc.mul⁻¹ Sc.mul-inv Sc.mul-natural Sc.Scone-p₁

    module Glued = Category G.cat
    open G.Obj
    open G._=>_
    open G._≃m_
    open setoid-predicate.Predicate
    open setoid-predicate._⊑_

    GF : Functor 𝒞 G.cat
    GF .fobj x .carrier = F .fobj x
    GF .fobj x .pred .pred f = ∃ (Env 𝒞.⇒ x) λ g → F .fmor g 𝒟.≈ f
    GF .fobj x .pred .pred-≃ f₁≈f₂ (g , eq) = g , 𝒟.≈-trans eq f₁≈f₂
    GF .fmor f .morph = F .fmor f
    GF .fmor f .presv .*⊑* f' (g , eq) =
      (f 𝒞.∘ g) , (begin
        F .fmor (f 𝒞.∘ g)        ≈⟨ F .fmor-comp f g ⟩
        F .fmor f 𝒟.∘ F .fmor g  ≈⟨ 𝒟.∘-cong 𝒟.≈-refl eq ⟩
        F .fmor f 𝒟.∘ f'         ∎)
      where open ≈-Reasoning 𝒟.isEquiv
    GF .fmor-cong f₁≈f₂ .f≃f = F .fmor-cong f₁≈f₂
    GF .fmor-id .f≃f = F .fmor-id
    GF .fmor-comp f g .f≃f = F .fmor-comp f g

    module _ where
      open FPFunctor
      open IsTerminal
      open IsProduct

      -- If F preserves finite products, then so does GF.
      GF-FP : FPFunctor GF
      GF-FP .preserve-terminal t t-isTerminal .to-terminal .morph =
        FP .preserve-terminal t t-isTerminal .to-terminal
      GF-FP .preserve-terminal t t-isTerminal .to-terminal {X} .presv .*⊑* g g∈X =
        t-isTerminal .to-terminal ,
        IsTerminal.to-terminal-unique (FP .preserve-terminal t t-isTerminal) _ _
      GF-FP .preserve-terminal t t-isTerminal .to-terminal-ext f .f≃f =
        FP .preserve-terminal t t-isTerminal .to-terminal-ext _

      GF-FP .preserve-products x y xy p₁ p₂ is-product .pair f g .morph =
        FP .preserve-products x y xy p₁ p₂ is-product .pair (f .morph) (g .morph)
      GF-FP .preserve-products x y xy p₁ p₂ is-product .pair {Z} f g .presv .*⊑* h h∈Z with f .presv .*⊑* h h∈Z
      ... | h₁ , eq₁ with g .presv .*⊑* h h∈Z
      ... | h₂ , eq₂ =
        is-product .pair h₁ h₂ ,
        (begin
          F .fmor (pair is-product h₁ h₂)
        ≈˘⟨ PP.pair-ext _ ⟩
          PP.pair (F .fmor p₁ 𝒟.∘ F .fmor (pair is-product h₁ h₂)) (F .fmor p₂ 𝒟.∘ F .fmor (pair is-product h₁ h₂))
        ≈˘⟨ PP.pair-cong (F .fmor-comp _ _) (F .fmor-comp _ _) ⟩
          PP.pair (F .fmor (p₁ 𝒞.∘ pair is-product h₁ h₂)) (F .fmor (p₂ 𝒞.∘ pair is-product h₁ h₂))
        ≈⟨ PP.pair-cong (F .fmor-cong (is-product .pair-p₁ _ _)) (F .fmor-cong (is-product .pair-p₂ _ _)) ⟩
          PP.pair (F .fmor h₁) (F .fmor h₂)
        ≈⟨ PP.pair-cong eq₁ eq₂ ⟩
          PP.pair (f .morph 𝒟.∘ h) (g .morph 𝒟.∘ h)
        ≈˘⟨ PP.pair-natural _ _ _ ⟩
          PP.pair (f .morph) (g .morph) 𝒟.∘ h
        ∎)
        where open ≈-Reasoning 𝒟.isEquiv
              module PP = IsProduct (FP .preserve-products x y xy p₁ p₂ is-product)
      GF-FP .preserve-products x y xy p₁ p₂ is-product .pair-cong f₁≈f₂ g₁≈g₂ .f≃f =
        FP .preserve-products _ _ _ _ _ is-product .pair-cong (f₁≈f₂ .f≃f) (g₁≈g₂ .f≃f)
      GF-FP .preserve-products x y xy p₁ p₂ is-product .pair-p₁ f g .f≃f =
        FP .preserve-products _ _ _ _ _ is-product .pair-p₁ _ _
      GF-FP .preserve-products x y xy p₁ p₂ is-product .pair-p₂ f g .f≃f =
        FP .preserve-products _ _ _ _ _ is-product .pair-p₂ _ _
      GF-FP .preserve-products x y xy p₁ p₂ is-product .pair-ext f .f≃f =
        FP .preserve-products _ _ _ _ _ is-product .pair-ext _

    thm : ∀ Y → (f : GF .fobj Env Glued.⇒ GF .fobj Y) → ∃ (Env 𝒞.⇒ Y) (λ g → F .fmor g 𝒟.≈ f .morph)
    thm Y f with f .presv .*⊑* (F .fmor (𝒞.id _)) (𝒞.id _ , 𝒟.≈-refl)
    ... | g , eq = g , (begin
                          F .fmor g                          ≈⟨ eq ⟩
                          f .morph 𝒟.∘ F .fmor (𝒞.id _)     ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-id) ⟩
                          f .morph 𝒟.∘ 𝒟.id _               ≈⟨ 𝒟.id-right ⟩
                          f .morph                           ∎)
      where open ≈-Reasoning 𝒟.isEquiv

    module LI = language-interpretation
                  Sig G.cat GPE.terminal GPE.products GPE.exponentials
                  (coproducts+exp→booleans GPE.terminal GCP.coproducts GPE.exponentials)
                  (transport-model Sig GF GF-FP {!!} Int)

    open L

    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    open 𝒟.Iso

    type-interp-iso : (τ : type) → 𝒟.Iso (LI.⟦ τ ⟧ty .carrier) 𝒟Interp.⟦ τ ⟧ty
    type-interp-iso unit .fwd = 𝒟T .HasTerminal.is-terminal .IsTerminal.to-terminal
    type-interp-iso unit .bwd = 𝒟T .HasTerminal.is-terminal .IsTerminal.to-terminal
    type-interp-iso unit .fwd∘bwd≈id = IsTerminal.to-terminal-unique (𝒟T .HasTerminal.is-terminal) _ _
    type-interp-iso unit .bwd∘fwd≈id = IsTerminal.to-terminal-unique (𝒟T .HasTerminal.is-terminal) _ _
    type-interp-iso bool .fwd = {!   !}
    type-interp-iso bool .bwd = {!   !}
    type-interp-iso bool .fwd∘bwd≈id = {!   !}
    type-interp-iso bool .bwd∘fwd≈id = {!   !}
    type-interp-iso (base s) = {!   !}
    type-interp-iso (σ [×] τ) = {!   !}
    type-interp-iso (σ [→] τ) = {!   !}

    ctxt-interp-iso : (Γ : ctxt) → 𝒟.Iso (LI.⟦ Γ ⟧ctxt .carrier) 𝒟Interp.⟦ Γ ⟧ctxt
    ctxt-interp-iso L.emp .fwd = 𝒟T .HasTerminal.is-terminal .IsTerminal.to-terminal
    ctxt-interp-iso L.emp .bwd = 𝒟T .HasTerminal.is-terminal .IsTerminal.to-terminal
    ctxt-interp-iso L.emp .fwd∘bwd≈id = IsTerminal.to-terminal-unique (𝒟T .HasTerminal.is-terminal) _ _
    ctxt-interp-iso L.emp .bwd∘fwd≈id = IsTerminal.to-terminal-unique (𝒟T .HasTerminal.is-terminal) _ _
    ctxt-interp-iso (Γ L., τ) = {!   !}

    project-all : ∀ {Γ τ} (M : Γ ⊢ τ) →
                  LI.⟦ M ⟧tm .morph 𝒟.≈ {!!} -- 𝒟Interp.⟦ M ⟧tm
    project-all = {!!}

  open L

  ⟦_⟧fo : ∀ {τ} → L.first-order τ → 𝒞.obj
  ⟦ unit ⟧fo = 𝒞T .HasTerminal.witness
  ⟦ bool ⟧fo = {!!}
  ⟦ base s ⟧fo = Int .Model.⟦sort⟧ s
  ⟦ τ₁ [×] τ₂ ⟧fo = 𝒞P .HasProducts.prod ⟦ τ₁ ⟧fo ⟦ τ₂ ⟧fo

  ⟦_⟧fo-ctxt : ∀ {Γ} → first-order-ctxt Γ → 𝒞.obj
  ⟦ emp ⟧fo-ctxt = 𝒞T .HasTerminal.witness
  ⟦ Γ L., τ ⟧fo-ctxt = 𝒞P .HasProducts.prod ⟦ Γ ⟧fo-ctxt ⟦ τ ⟧fo

  -- The interpretation of first-order types is isomorphic
  --    FIXME: this ought to be done in the glued category?
  fo-iso : ∀ {τ} (τ-fo : first-order τ) → 𝒟.Iso (F .fobj ⟦ τ-fo ⟧fo) (𝒟Interp.⟦ τ ⟧ty)
  fo-iso = {!!}

  fo-ctxt-iso : ∀ {Γ} (Γ-fo : first-order-ctxt Γ) → 𝒟.Iso (F .fobj ⟦ Γ-fo ⟧fo-ctxt) (𝒟Interp.⟦ Γ ⟧ctxt)
  fo-ctxt-iso = {!!}

  thm2 : ∀ {Γ τ} →
         (Γ-fo : first-order-ctxt Γ) →
         (τ-fo : first-order τ) →
         (M : Γ ⊢ τ) →
         ∃ (⟦ Γ-fo ⟧fo-ctxt 𝒞.⇒ ⟦ τ-fo ⟧fo)
           λ g → F .fmor g 𝒟.≈
                 (𝒟.Iso.bwd (fo-iso τ-fo) 𝒟.∘ (𝒟Interp.⟦ M ⟧tm 𝒟.∘ 𝒟.Iso.fwd (fo-ctxt-iso Γ-fo)))
  thm2 {Γ} {τ} Γ-fo τ-fo M = {!thm ⟦ τ-fo ⟧fo ⟦M⟧' !}
    where open glued ⟦ Γ-fo ⟧fo-ctxt
          ⟦M⟧ : LI.⟦ Γ ⟧ctxt Glued.⇒ LI.⟦ τ ⟧ty
          ⟦M⟧ = LI.⟦ M ⟧tm

          ⟦M⟧' : GF .fobj ⟦ Γ-fo ⟧fo-ctxt Glued.⇒ GF .fobj ⟦ τ-fo ⟧fo
          ⟦M⟧' = {!!} Glued.∘ (⟦M⟧ Glued.∘ {!!})

          eq : ⟦M⟧' .G._=>_.morph 𝒟.≈ (𝒟.Iso.bwd (fo-iso τ-fo) 𝒟.∘ (𝒟Interp.⟦ M ⟧tm 𝒟.∘ 𝒟.Iso.fwd (fo-ctxt-iso Γ-fo)))
          eq = {!!}
