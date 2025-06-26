{-# OPTIONS --postfix-projections --prop --safe #-}

module glueing-application where

open import Level using (suc; 0ℓ; lift)
open import prop using (_⇔_; _,_; proj₁; proj₂; ∃)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import prop-setoid using (IsEquivalence; module ≈-Reasoning)
open import categories using (Category; HasTerminal; HasProducts; HasCoproducts)
open import functor using (HasLimits; op-colimit; limits→limits'; Functor)
open import cmon-category using (CMonCategory)
open import product-category using (product; product-limit)
open import setoid-cat using (SetoidCat; Setoid-products; Setoid-coproducts)
import preorder
import galois
import cmon-enriched
import product-diagram
import empty-diagram
import meet-semilattice-category
import join-semilattice-category
import grothendieck
import fam

open Functor

------------------------------------------------------------------------------
module Galois = Category galois.cat

------------------------------------------------------------------------------
-- Meet × Join^op

M×Jop : CMonCategory (suc 0ℓ) 0ℓ 0ℓ
M×Jop .CMonCategory.cat =
  product meet-semilattice-category.cat (Category.opposite join-semilattice-category.cat)
M×Jop .CMonCategory.cmon-enriched =
  product-cmon-enriched meet-semilattice-category.cmon-enriched
                       (op-cmon-enriched join-semilattice-category.cmon-enriched)
  where open import cmon-enriched using (product-cmon-enriched; op-cmon-enriched)

M×Jop₀ = CMonCategory.cat M×Jop

module M×Jop₀ = Category M×Jop₀

module _ where

  𝓖 : Functor galois.cat M×Jop₀
  𝓖 .fobj X =
    record { carrier = X .galois.Obj.carrier ; meets = X .galois.Obj.meets } ,
    record { carrier = X .galois.Obj.carrier ; joins = X .galois.Obj.joins }
  𝓖 .fmor f =
    record { *→* = galois._⇒g_.right-∧ f } ,
    record { *→* = galois._⇒g_.left-∨ f }
  𝓖 .fmor-cong f≃g =
    record { f≃f = record { eqfunc = f≃g .galois._≃g_.right-eq } } ,
    record { f≃f = record { eqfunc = f≃g .galois._≃g_.left-eq } }
  𝓖 .fmor-id {X} =
    record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } } ,
    record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } }
  𝓖 .fmor-comp f g =
    (record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } }) ,
    (record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } })

Approx : Category.obj M×Jop₀
Approx = 𝓖 .fobj galois.TWO

M×Jop₀-limits-0 : ∀ (𝒮 : Category 0ℓ 0ℓ 0ℓ) → HasLimits 𝒮 M×Jop₀
M×Jop₀-limits-0 𝒮 D =
  product-limit _ _ 𝒮 D
    (meet-semilattice-category.limits 𝒮 _)
    (op-colimit _ (join-semilattice-category.colimits (Category.opposite 𝒮) _))

M×Jop-products : HasProducts M×Jop₀
M×Jop-products = product-diagram.limits→products M×Jop₀ (M×Jop₀-limits-0 _)

M×Jop-terminal : HasTerminal M×Jop₀
M×Jop-terminal = empty-diagram.limits→terminal M×Jop₀ (M×Jop₀-limits-0 _)

M×Jop-biproducts : ∀ x y → cmon-enriched.Biproduct (CMonCategory.cmon-enriched M×Jop) x y
M×Jop-biproducts =
  cmon-enriched.cmon+products→biproducts (M×Jop .CMonCategory.cmon-enriched) M×Jop-products

------------------------------------------------------------------------------
-- Fam(Meet × Join^op)

open grothendieck.CategoryOfFamilies 0ℓ 0ℓ M×Jop₀
  renaming ( cat        to Fam⟨M×Jop⟩
           ; terminal   to make-terminal
           ; coproducts to Fam⟨M×Jop⟩-coproducts
           ; _≃_        to Mor-≃)
  using (module products; Obj; Mor)
  public

Fam⟨M×Jop⟩-terminal : HasTerminal Fam⟨M×Jop⟩
Fam⟨M×Jop⟩-terminal = make-terminal M×Jop-terminal

open import families-exponentials 0ℓ 0ℓ
   M×Jop₀
   (M×Jop .CMonCategory.cmon-enriched)
   M×Jop-biproducts
   (fam.hasSetoidProducts 0ℓ 0ℓ M×Jop₀ λ A → limits→limits' (M×Jop₀-limits-0 _))
  renaming ( exponentials to Fam⟨M×Jop⟩-exponentials
           ; products     to Fam⟨M×Jop⟩-products )
  using    ()
  public

module _ where

  open Obj
  open fam.Fam

  Fam⟨Approx⟩ : Category.obj Fam⟨M×Jop⟩
  Fam⟨Approx⟩ .idx = prop-setoid.𝟙
  Fam⟨Approx⟩ .fam .fm _ = Approx
  Fam⟨Approx⟩ .fam .subst _ = Category.id M×Jop₀ _
  Fam⟨Approx⟩ .fam .refl* = Category.≈-refl M×Jop₀
  Fam⟨Approx⟩ .fam .trans* e₁ e₂ = Category.≈-sym M×Jop₀ (Category.id-left M×Jop₀)

  -- and this is a monoid wrt the finite products

  -- and there are some base types, interpreted as Sets

------------------------------------------------------------------------------
import two
import sconing
import glueing-simple
import setoid-predicate

-- FIXME: do Sconing with respect to n-ary products of Fam⟨Approx⟩
module Sc = sconing Fam⟨M×Jop⟩ Fam⟨M×Jop⟩-products Fam⟨Approx⟩
open Sc using (Scone)

module G = glueing-simple
             Fam⟨M×Jop⟩
             (SetoidCat 0ℓ 0ℓ) (Setoid-products 0ℓ 0ℓ) (Setoid-coproducts 0ℓ 0ℓ) setoid-predicate.system
             Sc.Scone

module Glued = Category G.cat

module GCP = G.coproducts Fam⟨M×Jop⟩-coproducts

module GP = G.products-and-exponentials
               Fam⟨M×Jop⟩-products
               Fam⟨M×Jop⟩-exponentials
               Sc.mul
               Sc.mul⁻¹
               Sc.mul-inv
               Sc.mul-natural
               Sc.Scone-p₁

-- Now have a BiCCC

module _ where
  open setoid-predicate.Predicate
  open Mor
  open Mor-≃
  open fam._⇒f_
  open fam._≃f_
  open meet-semilattice-category._⇒_
  open join-semilattice-category._⇒_
  open preorder._=>_

  -- The glued interpretation of the approximation object is that it
  -- is a galois connection with the environment.
  G⟨Approx⟩ : Glued.obj
  G⟨Approx⟩ .G.Obj.carrier = Fam⟨Approx⟩
  G⟨Approx⟩ .G.Obj.pred .pred f =
    ∃ (galois.TWO Galois.⇒ galois.TWO)
      (λ g → Category._≈_ M×Jop₀ (𝓖 .fmor g) (f .famf .transf (lift tt)))
  G⟨Approx⟩ .G.Obj.pred .pred-≃ {f₁} {f₂} f₁≈f₂ (g , eq) =
    g , (begin
      𝓖 .fmor g                                        ≈⟨ eq ⟩
      f₁ .famf .transf (lift tt)                       ≈˘⟨ M×Jop₀.id-left ⟩
      M×Jop₀.id _ M×Jop₀.∘ f₁ .famf .transf (lift tt)  ≈⟨ f₁≈f₂ .famf-eq .transf-eq {lift tt} ⟩
      f₂ .famf .transf (lift tt)                       ∎)
    where open ≈-Reasoning M×Jop₀.isEquiv

-- For any first-order type, and base element of the type, there is an
-- 'n ∈ ℕ' such that Fam⟨M×Jop⟩(Approx^n, ⟦ A ⟧) is an isomorphism in
-- the lower part.

-- Test theorem: A morphism G⟨Approx⟩ ⇒ G⟨Approx⟩ in G.cat must be a
-- galois connection at the lower level. In particular, the meet
-- semilattice and and join semilattice are isormorphic, and

-- 4. There is an approximation object in Glued(Scone(𝔸n))
--    - which ensures Galois connections by construction
-- 5. Derive the correctness properties:
--    (a) For every x : A ⊢ M : B, with A, B first order, ∀ a → ⟦ M ⟧ .famf a is a galois connection
--    (b) For every x : A ⊢ M : B, the set theoretic portions are equal. (sconing over 𝔸0)

-- Ideally:
-- 1. Fam(PSh_Cmon(GraphLang)) is a correct normaliser


-- data fo-type : Set where
--   `base `approx : fo-type
--   _`×_ _`+_ : fo-type → fo-type → fo-type
