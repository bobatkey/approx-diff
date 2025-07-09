{-# OPTIONS --postfix-projections --prop --safe #-}

module ho-model where

open import Level using (0ℓ; suc)
open import categories using (Category; HasProducts; HasTerminal; op-coproducts→products; op-initial→terminal; HasCoproducts)
open import product-category using (product; product-limit; product-products; product-terminal)
open import cmon-enriched
  using (CMonEnriched; product-cmon-enriched; op-cmon-enriched; Biproduct; biproducts→products)
open import functor using (HasLimits; op-colimit; limits→limits')
import meet-semilattice-category
import join-semilattice-category
import fam
import indexed-family

------------------------------------------------------------------------------
-- Construct Meet × Join^op

M×Jop : Category (suc 0ℓ) 0ℓ 0ℓ
M×Jop = product meet-semilattice-category.cat (Category.opposite join-semilattice-category.cat)

private
  module M×Jop = Category M×Jop

M×Jop-cmon-enriched : CMonEnriched M×Jop
M×Jop-cmon-enriched =
  product-cmon-enriched
    meet-semilattice-category.cmon-enriched
    (op-cmon-enriched join-semilattice-category.cmon-enriched)

M×Jop-limits : ∀ (𝒮 : Category 0ℓ 0ℓ 0ℓ) → HasLimits 𝒮 M×Jop
M×Jop-limits 𝒮 D =
  product-limit _ _ 𝒮 D
    (meet-semilattice-category.limits 𝒮 _)
    (op-colimit _ (join-semilattice-category.colimits (Category.opposite 𝒮) _))

-- We make the products and terminal object "by hand" so that the
-- representations used for programs are nice.

M×Jop-terminal : HasTerminal M×Jop
M×Jop-terminal =
  product-terminal _ _ meet-semilattice-category.terminal
                       (op-initial→terminal join-semilattice-category.initial)

M×Jop-biproducts : ∀ x y → cmon-enriched.Biproduct M×Jop-cmon-enriched x y
M×Jop-biproducts =
  cmon-enriched.cmon+products→biproducts M×Jop-cmon-enriched
    (product-products _ _
      meet-semilattice-category.products
      (op-coproducts→products join-semilattice-category.coproducts))

M×Jop-products : HasProducts M×Jop
M×Jop-products = biproducts→products _ M×Jop-biproducts

------------------------------------------------------------------------------
-- Functor from LatGal to Meet×Join^op, which preserves finite products

import galois
import preorder
open import functor using (Functor)
open import Data.Product using (_,_; proj₁; proj₂)
open import prop using (_,_)
open import prop-setoid using (IsEquivalence)
open import finite-product-functor
  using (preserve-chosen-products; preserve-chosen-terminal)

open Functor

𝓖 : Functor galois.cat M×Jop
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

module _ where

  import meet-semilattice
  import join-semilattice
  open M×Jop.IsIso
  open import prop using (tt; proj₁; proj₂)

  𝓖-preserve-terminal : preserve-chosen-terminal 𝓖 galois.terminal M×Jop-terminal
  𝓖-preserve-terminal .inverse =
    record { *→* = meet-semilattice.terminal } ,
    record { *→* = join-semilattice.initial }
  𝓖-preserve-terminal .f∘inverse≈id =
    HasTerminal.to-terminal-unique M×Jop-terminal _ _
  𝓖-preserve-terminal .inverse∘f≈id =
    record { f≃f = record { eqfunc = record { eqfun = λ x → tt , tt } } } ,
    record { f≃f = record { eqfunc = record { eqfun = λ x → tt , tt } } }

  open meet-semilattice-category._⇒_
  open join-semilattice-category._⇒_
  open meet-semilattice-category._≃m_
  open join-semilattice-category._≃m_
  open meet-semilattice._≃m_
  open join-semilattice._≃m_
  open preorder._≃m_
  open galois.Obj

  𝓖-preserve-products : preserve-chosen-products 𝓖 galois.products (biproducts→products _ M×Jop-biproducts)
  𝓖-preserve-products .inverse .proj₁ .*→* = meet-semilattice.id
  𝓖-preserve-products .inverse .proj₂ .*→* = join-semilattice.id
  𝓖-preserve-products {X} {Y} .f∘inverse≈id .proj₁ .f≃f .eqfunc .eqfun (x , y) =
    (X .π₁ , Y .π₂) ,
    (X .⟨_∧_⟩ (X .≤-refl) (X .≤-top) , Y .⟨_∧_⟩ (Y .≤-top) (Y .≤-refl))
  𝓖-preserve-products {X} {Y} .f∘inverse≈id .proj₂ .f≃f .eqfunc .eqfun (x , y) =
    (X .[_∨_] (X .[_∨_] (X .≤-refl) (X .≤-bottom)) (X .≤-bottom) ,
     Y .[_∨_] (Y .≤-bottom) (Y .[_∨_] (Y .≤-bottom) (Y .≤-refl))) ,
    (X .≤-trans (X .inl) (X .inl) , Y .≤-trans (Y .inr) (Y .inr))
  𝓖-preserve-products {X} {Y} .inverse∘f≈id .proj₁ .f≃f .eqfunc .eqfun (x , y) =
    (X .π₁ , Y .π₂) ,
    (X .⟨_∧_⟩ (X .≤-refl) (X .≤-top) , Y .⟨_∧_⟩ (Y .≤-top) (Y .≤-refl))
  𝓖-preserve-products {X} {Y} .inverse∘f≈id .proj₂ .f≃f .eqfunc .eqfun (x , y) =
    (X .[_∨_] (X .[_∨_] (X .≤-refl) (X .≤-bottom)) (X .≤-bottom) ,
     Y .[_∨_] (Y .≤-bottom) (Y .[_∨_] (Y .≤-bottom) (Y .≤-refl))) ,
    (X .≤-trans (X .inl) (X .inl) , Y .≤-trans (Y .inr) (Y .inr))

------------------------------------------------------------------------------
-- Fam(Meet × Join^op)

module Fam⟨M×Jop⟩ = fam.CategoryOfFamilies 0ℓ 0ℓ M×Jop

open Fam⟨M×Jop⟩ using ()
  renaming ( cat to Fam⟨M×Jop⟩-cat
           ; coproducts to Fam⟨M×Jop⟩-coproducts
           ; bigCoproducts to Fam⟨M×Jop⟩-bigCoproducts
           )

Fam⟨M×Jop⟩-terminal : HasTerminal Fam⟨M×Jop⟩-cat
Fam⟨M×Jop⟩-terminal = Fam⟨M×Jop⟩.terminal M×Jop-terminal

open import fam-exponentials 0ℓ 0ℓ
  M×Jop
  M×Jop-cmon-enriched
  M×Jop-biproducts
  (indexed-family.hasSetoidProducts 0ℓ 0ℓ M×Jop λ A → limits→limits' (M×Jop-limits _))
  renaming ( exponentials to Fam⟨M×Jop⟩-exponentials
           ; products     to Fam⟨M×Jop⟩-products
           )
  using ()

import lists

Fam⟨M×Jop⟩-lists = lists.lists Fam⟨M×Jop⟩-cat Fam⟨M×Jop⟩-terminal Fam⟨M×Jop⟩-products Fam⟨M×Jop⟩-exponentials Fam⟨M×Jop⟩-bigCoproducts

Fam⟨M×Jop⟩-bool =
  Fam⟨M×Jop⟩-coproducts .HasCoproducts.coprod
    (Fam⟨M×Jop⟩-terminal .HasTerminal.witness)
    (Fam⟨M×Jop⟩-terminal .HasTerminal.witness)

------------------------------------------------------------------------------
-- Functor from Fam⟨LatGal⟩ to Fam⟨M×Jop⟩

module Fam⟨LatGal⟩ = fam.CategoryOfFamilies 0ℓ 0ℓ galois.cat

Fam⟨LatGal⟩-coproducts = Fam⟨LatGal⟩.coproducts
Fam⟨LatGal⟩-terminal = Fam⟨LatGal⟩.terminal galois.terminal
Fam⟨LatGal⟩-products = Fam⟨LatGal⟩.products.products galois.products
Fam⟨LatGal⟩-bool =
  Fam⟨LatGal⟩-coproducts .HasCoproducts.coprod
    (Fam⟨LatGal⟩-terminal .HasTerminal.witness)
    (Fam⟨LatGal⟩-terminal .HasTerminal.witness)

open import fam-functor using (FamF)

Fam⟨𝓖⟩ : Functor Fam⟨LatGal⟩.cat Fam⟨M×Jop⟩.cat
Fam⟨𝓖⟩ = FamF 0ℓ 0ℓ 𝓖

Fam⟨𝓖⟩-preserves-products =
  fam-functor.preserve-products 0ℓ 0ℓ 𝓖 galois.products M×Jop-products (λ {X} {Y} → 𝓖-preserve-products {X} {Y})

Fam⟨𝓖⟩-preserves-coproducts =
  fam-functor.preserve-coproducts 0ℓ 0ℓ 𝓖

Fam⟨𝓖⟩-preserves-terminal =
  fam-functor.preserve-terminal 0ℓ 0ℓ 𝓖 galois.terminal M×Jop-terminal 𝓖-preserve-terminal

Fam⟨𝓖⟩-preserves-bool : Fam⟨M×Jop⟩.Mor (Fam⟨𝓖⟩ .fobj Fam⟨LatGal⟩-bool) Fam⟨M×Jop⟩-bool
Fam⟨𝓖⟩-preserves-bool =
  Fam⟨M×Jop⟩.Mor-∘ (HasCoproducts.coprod-m Fam⟨M×Jop⟩-coproducts (Fam⟨M×Jop⟩-terminal .HasTerminal.to-terminal) (Fam⟨M×Jop⟩-terminal .HasTerminal.to-terminal))
                    (Fam⟨𝓖⟩-preserves-coproducts .Category.IsIso.inverse)

------------------------------------------------------------------------------
-- For any signature and implementation in Fam⟨LatGal⟩, we get an
-- interpretation of the language in Fam⟨M×Jop⟩

open import signature

module interp (Sig : Signature 0ℓ)
              (Impl : Model PFPC[ Fam⟨LatGal⟩.cat , Fam⟨LatGal⟩-terminal , Fam⟨LatGal⟩-products , Fam⟨LatGal⟩-bool ] Sig)
   where

   open Fam⟨M×Jop⟩.Mor public
   open Fam⟨M×Jop⟩.Obj public

   open import language-interpretation Sig
     Fam⟨M×Jop⟩-cat
     Fam⟨M×Jop⟩-terminal
     Fam⟨M×Jop⟩-products
     Fam⟨M×Jop⟩-coproducts
     Fam⟨M×Jop⟩-exponentials
     Fam⟨M×Jop⟩-lists
     (transport-model Sig Fam⟨𝓖⟩ Fam⟨𝓖⟩-preserves-terminal Fam⟨𝓖⟩-preserves-products Fam⟨𝓖⟩-preserves-bool Impl)
     public
