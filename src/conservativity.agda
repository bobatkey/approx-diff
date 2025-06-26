{-# OPTIONS --postfix-projections --prop --safe #-}

module conservativity where

open import Level
open import prop using (_,_; proj₁; proj₂; ∃)
open import categories using (Category; HasProducts; HasCoproducts; HasExponentials; HasTerminal)
open import functor using (Functor)
open import prop-setoid using (module ≈-Reasoning)
open import setoid-cat using (SetoidCat)
import sconing
import glueing-simple
import setoid-predicate

open Functor

module _ {o m e}
         (𝒞 : Category o m e)
         (𝒟 : Category o m e)
         (𝒟T : HasTerminal 𝒟) (𝒟P : HasProducts 𝒟) (𝒟CP : HasCoproducts 𝒟) (𝒟E : HasExponentials 𝒟 𝒟P)
         (F  : Functor 𝒞 𝒟)
  where

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟

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

    -- FIXME: if F preserves finite products, then so does GF.

    thm : ∀ Y → (f : GF .fobj Env Glued.⇒ GF .fobj Y) → ∃ (Env 𝒞.⇒ Y) (λ g → F .fmor g 𝒟.≈ f .morph)
    thm Y f with f .presv .*⊑* (F .fmor (𝒞.id _)) (𝒞.id _ , 𝒟.≈-refl)
    ... | g , eq = g , (begin
                          F .fmor g                          ≈⟨ eq ⟩
                          f .morph 𝒟.∘ F .fmor (𝒞.id _)     ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-id) ⟩
                          f .morph 𝒟.∘ 𝒟.id _               ≈⟨ 𝒟.id-right ⟩
                          f .morph                           ∎)
      where open ≈-Reasoning 𝒟.isEquiv

-- Let Sig be a signature
-- Let M be a model of Sig in 𝒞, and F be a finite product and infinite coproduct preserving functor
-- Then:
--   1. Can interpret the whole language in Glued
--   2. Every first order type is isomorphic to its interpretation in 𝒞
--   3. So every judgement x : A ⊢ M : B, with A, B first-order, has a morphism g : A 𝒞.⇒ B such that F(g) = ⟦ M ⟧

-- Could also replay the whole thing with `Stable` instead of Fam⟨LatGal⟩ ??





-- For the actual language:
--  1. 𝒞 = Fam⟨Gal⟩ which has finite products and infinite coproducts
--  2. 𝒟 = Fam⟨M×Jop⟩ which is a BiCCC
--  3. F  = Fam⟨𝓖⟩ which preserves products and infinite coproducts
