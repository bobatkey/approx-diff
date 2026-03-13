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
-- Construct Join × Join^op

J×Jop : Category (suc 0ℓ) 0ℓ 0ℓ
J×Jop = product join-semilattice-category.cat (Category.opposite join-semilattice-category.cat)

J×Jop-cmon-enriched : CMonEnriched J×Jop
J×Jop-cmon-enriched =
  product-cmon-enriched
    join-semilattice-category.cmon-enriched
    (op-cmon-enriched join-semilattice-category.cmon-enriched)

J×Jop-limits : ∀ (𝒮 : Category 0ℓ 0ℓ 0ℓ) → HasLimits 𝒮 J×Jop
J×Jop-limits 𝒮 D =
  product-limit _ _ 𝒮 D
    (join-semilattice-category.limits 𝒮 _)
    (op-colimit _ (join-semilattice-category.colimits (Category.opposite 𝒮) _))

J×Jop-terminal : HasTerminal J×Jop
J×Jop-terminal =
  product-terminal _ _ join-semilattice-category.terminal
                       (op-initial→terminal join-semilattice-category.initial)

J×Jop-biproducts : ∀ x y → cmon-enriched.Biproduct J×Jop-cmon-enriched x y
J×Jop-biproducts =
  cmon-enriched.cmon+products→biproducts J×Jop-cmon-enriched
    (product-products _ _
      join-semilattice-category.products
      (op-coproducts→products join-semilattice-category.coproducts))

J×Jop-products : HasProducts J×Jop
J×Jop-products = biproducts→products _ J×Jop-biproducts

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
-- Functor from HeytConj to Join×Join^op, which preserves finite products

import conjugate

𝓒 : Functor conjugate.cat J×Jop
𝓒 .fobj X =
  record { carrier = X .conjugate.Obj.carrier ; joins = X .conjugate.Obj.joins } ,
  record { carrier = X .conjugate.Obj.carrier ; joins = X .conjugate.Obj.joins }
𝓒 .fmor f =
  record { *→* = conjugate._⇒c_.right-∨ f } ,
  record { *→* = conjugate._⇒c_.left-∨ f }
𝓒 .fmor-cong f≃g =
  record { f≃f = record { eqfunc = f≃g .conjugate._≃c_.right-eq } } ,
  record { f≃f = record { eqfunc = f≃g .conjugate._≃c_.left-eq } }
𝓒 .fmor-id {X} =
  record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } } ,
  record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } }
𝓒 .fmor-comp f g =
  (record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } }) ,
  (record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } })

module _ where

  private
    module J×Jop = Category J×Jop

  import join-semilattice
  open J×Jop.IsIso
  open import prop using (tt; proj₁; proj₂)

  𝓒-preserve-terminal : preserve-chosen-terminal 𝓒 conjugate.terminal J×Jop-terminal
  𝓒-preserve-terminal .inverse =
    record { *→* = join-semilattice.terminal } ,
    record { *→* = join-semilattice.initial }
  𝓒-preserve-terminal .f∘inverse≈id =
    HasTerminal.to-terminal-unique J×Jop-terminal _ _
  𝓒-preserve-terminal .inverse∘f≈id =
    record { f≃f = record { eqfunc = record { eqfun = λ x → tt , tt } } } ,
    record { f≃f = record { eqfunc = record { eqfun = λ x → tt , tt } } }

  open join-semilattice-category._⇒_
  open join-semilattice-category._≃m_
  open join-semilattice._≃m_
  open preorder._≃m_
  open conjugate.Obj

  𝓒-preserve-products : preserve-chosen-products 𝓒 conjugate.products (biproducts→products _ J×Jop-biproducts)
  𝓒-preserve-products .inverse .proj₁ .*→* = join-semilattice.id
  𝓒-preserve-products .inverse .proj₂ .*→* = join-semilattice.id
  𝓒-preserve-products {X} {Y} .f∘inverse≈id .proj₁ .f≃f .eqfunc .eqfun (x , y) =
    (X .[_∨_] (X .≤-refl) (X .≤-bottom) , Y .[_∨_] (Y .≤-bottom) (Y .≤-refl)) ,
    (X .inl , Y .inr)
  𝓒-preserve-products {X} {Y} .f∘inverse≈id .proj₂ .f≃f .eqfunc .eqfun (x , y) =
    (X .[_∨_] (X .[_∨_] (X .≤-refl) (X .≤-bottom)) (X .≤-bottom) ,
     Y .[_∨_] (Y .≤-bottom) (Y .[_∨_] (Y .≤-bottom) (Y .≤-refl))) ,
    (X .≤-trans (X .inl) (X .inl) , Y .≤-trans (Y .inr) (Y .inr))
  𝓒-preserve-products {X} {Y} .inverse∘f≈id .proj₁ .f≃f .eqfunc .eqfun (x , y) =
    (X .[_∨_] (X .≤-refl) (X .≤-bottom) , Y .[_∨_] (Y .≤-bottom) (Y .≤-refl)) ,
    (X .inl , Y .inr)
  𝓒-preserve-products {X} {Y} .inverse∘f≈id .proj₂ .f≃f .eqfunc .eqfun (x , y) =
    (X .[_∨_] (X .[_∨_] (X .≤-refl) (X .≤-bottom)) (X .≤-bottom) ,
     Y .[_∨_] (Y .≤-bottom) (Y .[_∨_] (Y .≤-bottom) (Y .≤-refl))) ,
    (X .≤-trans (X .inl) (X .inl) , Y .≤-trans (Y .inr) (Y .inr))

------------------------------------------------------------------------------
-- Given a CMon-enriched category 𝒟 with limits, terminal, and
-- biproducts, a source category 𝒞 with terminal and products, and a
-- finite-product-preserving functor F : 𝒞 → 𝒟, we get an
-- interpretation in Fam⟨𝒟⟩ from a model in Fam⟨𝒞⟩.

open import fam-functor using (FamF)
open import signature
import lists

module Interpretation
  (𝒞 : Category (suc 0ℓ) 0ℓ 0ℓ)
  (𝒞-terminal : HasTerminal 𝒞)
  (𝒞-products : HasProducts 𝒞)
  (𝒟 : Category (suc 0ℓ) 0ℓ 0ℓ)
  (𝒟-cmon : CMonEnriched 𝒟)
  (𝒟-limits : ∀ (𝒮 : Category 0ℓ 0ℓ 0ℓ) → HasLimits 𝒮 𝒟)
  (𝒟-terminal : HasTerminal 𝒟)
  (𝒟-biproducts : ∀ x y → Biproduct 𝒟-cmon x y)
  (F : Functor 𝒞 𝒟)
  (F-preserve-terminal : preserve-chosen-terminal F 𝒞-terminal 𝒟-terminal)
  (F-preserve-products : preserve-chosen-products F 𝒞-products (biproducts→products _ 𝒟-biproducts))
  where

  -- Target: Fam⟨𝒟⟩
  module Fam⟨𝒟⟩ = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒟

  Fam⟨𝒟⟩-terminal : HasTerminal Fam⟨𝒟⟩.cat
  Fam⟨𝒟⟩-terminal = Fam⟨𝒟⟩.terminal 𝒟-terminal

  Fam⟨𝒟⟩-coproducts = Fam⟨𝒟⟩.coproducts

  open import fam-exponentials 0ℓ 0ℓ
    𝒟 𝒟-cmon 𝒟-biproducts
    (indexed-family.hasSetoidProducts 0ℓ 0ℓ 𝒟 λ A → limits→limits' (𝒟-limits _))
    renaming ( exponentials to Fam⟨𝒟⟩-exponentials
             ; products     to Fam⟨𝒟⟩-products
             )
    using ()
    public

  Fam⟨𝒟⟩-lists = lists.lists Fam⟨𝒟⟩.cat Fam⟨𝒟⟩-terminal Fam⟨𝒟⟩-products Fam⟨𝒟⟩-exponentials Fam⟨𝒟⟩.bigCoproducts

  Fam⟨𝒟⟩-bool =
    Fam⟨𝒟⟩-coproducts .HasCoproducts.coprod
      (Fam⟨𝒟⟩-terminal .HasTerminal.witness)
      (Fam⟨𝒟⟩-terminal .HasTerminal.witness)

  -- Source: Fam⟨𝒞⟩
  module Fam⟨𝒞⟩ = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒞

  Fam⟨𝒞⟩-terminal = Fam⟨𝒞⟩.terminal 𝒞-terminal
  Fam⟨𝒞⟩-products = Fam⟨𝒞⟩.products.products 𝒞-products
  Fam⟨𝒞⟩-coproducts = Fam⟨𝒞⟩.coproducts

  Fam⟨𝒞⟩-bool =
    Fam⟨𝒞⟩-coproducts .HasCoproducts.coprod
      (Fam⟨𝒞⟩-terminal .HasTerminal.witness)
      (Fam⟨𝒞⟩-terminal .HasTerminal.witness)

  -- Lifted functor Fam⟨F⟩ : Fam⟨𝒞⟩ → Fam⟨𝒟⟩
  Fam⟨F⟩ : Functor Fam⟨𝒞⟩.cat Fam⟨𝒟⟩.cat
  Fam⟨F⟩ = FamF 0ℓ 0ℓ F

  Fam⟨F⟩-preserves-products =
    fam-functor.preserve-products 0ℓ 0ℓ F 𝒞-products (biproducts→products _ 𝒟-biproducts)
      (λ {X} {Y} → F-preserve-products {X} {Y})

  Fam⟨F⟩-preserves-coproducts =
    fam-functor.preserve-coproducts 0ℓ 0ℓ F

  Fam⟨F⟩-preserves-terminal =
    fam-functor.preserve-terminal 0ℓ 0ℓ F 𝒞-terminal 𝒟-terminal F-preserve-terminal

  Fam⟨F⟩-preserves-bool : Fam⟨𝒟⟩.Mor (Fam⟨F⟩ .fobj Fam⟨𝒞⟩-bool) Fam⟨𝒟⟩-bool
  Fam⟨F⟩-preserves-bool =
    Fam⟨𝒟⟩.Mor-∘ (HasCoproducts.coprod-m Fam⟨𝒟⟩-coproducts (Fam⟨𝒟⟩-terminal .HasTerminal.to-terminal) (Fam⟨𝒟⟩-terminal .HasTerminal.to-terminal))
                  (Fam⟨F⟩-preserves-coproducts .Category.IsIso.inverse)

  -- Interpretation
  module interp (Sig : Signature 0ℓ)
                (Impl : Model PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ] Sig)
     where

     open Fam⟨𝒟⟩.Mor public
     open Fam⟨𝒟⟩.Obj public

     open import language-interpretation Sig
       Fam⟨𝒟⟩.cat
       Fam⟨𝒟⟩-terminal
       Fam⟨𝒟⟩-products
       Fam⟨𝒟⟩-coproducts
       Fam⟨𝒟⟩-exponentials
       Fam⟨𝒟⟩-lists
       (transport-model Sig Fam⟨F⟩ Fam⟨F⟩-preserves-terminal Fam⟨F⟩-preserves-products Fam⟨F⟩-preserves-bool Impl)
       public

------------------------------------------------------------------------------
-- Concrete instantiations

module Galois = Interpretation
  galois.cat galois.terminal galois.products
  M×Jop M×Jop-cmon-enriched M×Jop-limits M×Jop-terminal M×Jop-biproducts
  𝓖 𝓖-preserve-terminal (λ {X} {Y} → 𝓖-preserve-products {X} {Y})

module Conjugate = Interpretation
  conjugate.cat conjugate.terminal conjugate.products
  J×Jop J×Jop-cmon-enriched J×Jop-limits J×Jop-terminal J×Jop-biproducts
  𝓒 𝓒-preserve-terminal (λ {X} {Y} → 𝓒-preserve-products {X} {Y})
