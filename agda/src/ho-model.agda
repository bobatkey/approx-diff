{-# OPTIONS --postfix-projections --prop --safe #-}

module ho-model where

open import Level using (Level; 0ℓ; suc)
open import categories using (Category; HasProducts; HasTerminal; HasInitial; op-coproducts→products; op-initial→terminal; HasCoproducts)
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

open import functor using (Functor)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import prop using (_,_)
open import prop-setoid using (IsEquivalence)
open import finite-product-functor
  using (preserve-chosen-products; preserve-chosen-terminal)

open Functor

------------------------------------------------------------------------------
-- Given a CMon-enriched category 𝒟 with limits, terminal, and
-- biproducts, a source category 𝒞 with terminal and products, and a
-- finite-product-preserving functor F : 𝒞 → 𝒟, we get an
-- interpretation in Fam⟨𝒟⟩ from a model in Fam⟨𝒞⟩.

open import fam-functor using (FamF)
open import signature
import lists

module Interpretation
  {o : Level}
  (𝒞 : Category o 0ℓ 0ℓ)
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

module Galois where
  import galois
  import preorder
  import meet-semilattice
  import join-semilattice
  open import prop using (tt; proj₁; proj₂)
  open meet-semilattice-category._⇒_
  open join-semilattice-category._⇒_
  open meet-semilattice-category._≃m_
  open join-semilattice-category._≃m_
  open meet-semilattice._≃m_
  open join-semilattice._≃m_
  open preorder._≃m_
  open galois.Obj

  𝓕 : Functor galois.cat M×Jop
  𝓕 .fobj X .proj₁ = record { carrier = X .galois.Obj.carrier ; meets = X .galois.Obj.meets }
  𝓕 .fobj X .proj₂ = record { carrier = X .galois.Obj.carrier ; joins = X .galois.Obj.joins }
  𝓕 .fmor f .proj₁ .*→* = galois._⇒g_.right-∧ f
  𝓕 .fmor f .proj₂ .*→* = galois._⇒g_.left-∨ f
  𝓕 .fmor-cong f≃g .proj₁ .f≃f .eqfunc = f≃g .galois._≃g_.right-eq
  𝓕 .fmor-cong f≃g .proj₂ .f≃f .eqfunc = f≃g .galois._≃g_.left-eq
  𝓕 .fmor-id .proj₁ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl
  𝓕 .fmor-id .proj₂ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl
  𝓕 .fmor-comp f g .proj₁ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl
  𝓕 .fmor-comp f g .proj₂ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl

  private
    module M×Jop' = Category M×Jop

  open M×Jop'.IsIso

  𝓕-preserve-terminal : preserve-chosen-terminal 𝓕 galois.terminal M×Jop-terminal
  𝓕-preserve-terminal .inverse .proj₁ .*→* = meet-semilattice.terminal
  𝓕-preserve-terminal .inverse .proj₂ .*→* = join-semilattice.initial
  𝓕-preserve-terminal .f∘inverse≈id =
    HasTerminal.to-terminal-unique M×Jop-terminal _ _
  𝓕-preserve-terminal .inverse∘f≈id .proj₁ .f≃f .eqfunc .eqfun x = tt , tt
  𝓕-preserve-terminal .inverse∘f≈id .proj₂ .f≃f .eqfunc .eqfun x = tt , tt

  𝓕-preserve-products : preserve-chosen-products 𝓕 galois.products (biproducts→products _ M×Jop-biproducts)
  𝓕-preserve-products .inverse .proj₁ .*→* = meet-semilattice.id
  𝓕-preserve-products .inverse .proj₂ .*→* = join-semilattice.id
  𝓕-preserve-products {X} {Y} .f∘inverse≈id .proj₁ .f≃f .eqfunc .eqfun (x , y) =
    (X .π₁ , Y .π₂) ,
    (X .⟨_∧_⟩ (X .≤-refl) (X .≤-top) , Y .⟨_∧_⟩ (Y .≤-top) (Y .≤-refl))
  𝓕-preserve-products {X} {Y} .f∘inverse≈id .proj₂ .f≃f .eqfunc .eqfun (x , y) =
    (X .[_∨_] (X .[_∨_] (X .≤-refl) (X .≤-bottom)) (X .≤-bottom) ,
     Y .[_∨_] (Y .≤-bottom) (Y .[_∨_] (Y .≤-bottom) (Y .≤-refl))) ,
    (X .≤-trans (X .inl) (X .inl) , Y .≤-trans (Y .inr) (Y .inr))
  𝓕-preserve-products {X} {Y} .inverse∘f≈id .proj₁ .f≃f .eqfunc .eqfun (x , y) =
    (X .π₁ , Y .π₂) ,
    (X .⟨_∧_⟩ (X .≤-refl) (X .≤-top) , Y .⟨_∧_⟩ (Y .≤-top) (Y .≤-refl))
  𝓕-preserve-products {X} {Y} .inverse∘f≈id .proj₂ .f≃f .eqfunc .eqfun (x , y) =
    (X .[_∨_] (X .[_∨_] (X .≤-refl) (X .≤-bottom)) (X .≤-bottom) ,
     Y .[_∨_] (Y .≤-bottom) (Y .[_∨_] (Y .≤-bottom) (Y .≤-refl))) ,
    (X .≤-trans (X .inl) (X .inl) , Y .≤-trans (Y .inr) (Y .inr))

  open Interpretation
    galois.cat galois.terminal galois.products
    M×Jop M×Jop-cmon-enriched M×Jop-limits M×Jop-terminal M×Jop-biproducts
    𝓕 𝓕-preserve-terminal (λ {X} {Y} → 𝓕-preserve-products {X} {Y})
    public

module Conjugate where
  import preorder
  import join-semilattice
  import conjugate
  open import prop using (tt; proj₁; proj₂)
  open join-semilattice-category._⇒_
  open join-semilattice-category._≃m_
  open join-semilattice._≃m_
  open preorder._≃m_
  open conjugate.Obj

  𝓕 : Functor conjugate.cat J×Jop
  𝓕 .fobj X .proj₁ = record { carrier = X .conjugate.Obj.carrier ; joins = X .conjugate.Obj.joins }
  𝓕 .fobj X .proj₂ = record { carrier = X .conjugate.Obj.carrier ; joins = X .conjugate.Obj.joins }
  𝓕 .fmor f .proj₁ .*→* = conjugate._⇒c_.right-∨ f
  𝓕 .fmor f .proj₂ .*→* = conjugate._⇒c_.left-∨ f
  𝓕 .fmor-cong f≃g .proj₁ .f≃f .eqfunc = f≃g .conjugate._≃c_.right-eq
  𝓕 .fmor-cong f≃g .proj₂ .f≃f .eqfunc = f≃g .conjugate._≃c_.left-eq
  𝓕 .fmor-id .proj₁ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl
  𝓕 .fmor-id .proj₂ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl
  𝓕 .fmor-comp f g .proj₁ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl
  𝓕 .fmor-comp f g .proj₂ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl

  private
    module J×Jop' = Category J×Jop

  open J×Jop'.IsIso

  𝓕-preserve-terminal : preserve-chosen-terminal 𝓕 conjugate.terminal J×Jop-terminal
  𝓕-preserve-terminal .inverse .proj₁ .*→* = join-semilattice.terminal
  𝓕-preserve-terminal .inverse .proj₂ .*→* = join-semilattice.initial
  𝓕-preserve-terminal .f∘inverse≈id =
    HasTerminal.to-terminal-unique J×Jop-terminal _ _
  𝓕-preserve-terminal .inverse∘f≈id .proj₁ .f≃f .eqfunc .eqfun x = tt , tt
  𝓕-preserve-terminal .inverse∘f≈id .proj₂ .f≃f .eqfunc .eqfun x = tt , tt

  𝓕-preserve-products : preserve-chosen-products 𝓕 conjugate.products (biproducts→products _ J×Jop-biproducts)
  𝓕-preserve-products .inverse .proj₁ .*→* = join-semilattice.id
  𝓕-preserve-products .inverse .proj₂ .*→* = join-semilattice.id
  𝓕-preserve-products {X} {Y} .f∘inverse≈id .proj₁ .f≃f .eqfunc .eqfun (x , y) =
    (X .[_∨_] (X .≤-refl) (X .≤-bottom) , Y .[_∨_] (Y .≤-bottom) (Y .≤-refl)) ,
    (X .inl , Y .inr)
  𝓕-preserve-products {X} {Y} .f∘inverse≈id .proj₂ .f≃f .eqfunc .eqfun (x , y) =
    (X .[_∨_] (X .[_∨_] (X .≤-refl) (X .≤-bottom)) (X .≤-bottom) ,
     Y .[_∨_] (Y .≤-bottom) (Y .[_∨_] (Y .≤-bottom) (Y .≤-refl))) ,
    (X .≤-trans (X .inl) (X .inl) , Y .≤-trans (Y .inr) (Y .inr))
  𝓕-preserve-products {X} {Y} .inverse∘f≈id .proj₁ .f≃f .eqfunc .eqfun (x , y) =
    (X .[_∨_] (X .≤-refl) (X .≤-bottom) , Y .[_∨_] (Y .≤-bottom) (Y .≤-refl)) ,
    (X .inl , Y .inr)
  𝓕-preserve-products {X} {Y} .inverse∘f≈id .proj₂ .f≃f .eqfunc .eqfun (x , y) =
    (X .[_∨_] (X .[_∨_] (X .≤-refl) (X .≤-bottom)) (X .≤-bottom) ,
     Y .[_∨_] (Y .≤-bottom) (Y .[_∨_] (Y .≤-bottom) (Y .≤-refl))) ,
    (X .≤-trans (X .inl) (X .inl) , Y .≤-trans (Y .inr) (Y .inr))

  open Interpretation
    conjugate.cat conjugate.terminal conjugate.products
    J×Jop J×Jop-cmon-enriched J×Jop-limits J×Jop-terminal J×Jop-biproducts
    𝓕 𝓕-preserve-terminal (λ {X} {Y} → 𝓕-preserve-products {X} {Y})
    public

module Matrix where
  import join-semilattice-category as SemiLat
  import cmon-enriched as CMon
  open import two using (Two; O; I)
  open import prop using (tt; proj₁)
  open import prop-setoid using (module ≈-Reasoning)
  import join-semilattice
  import preorder
  open SemiLat._≃m_
  open SemiLat._⇒_
  open join-semilattice._≃m_ using (eqfunc)
  open preorder._≃m_ using (eqfun)

  open Category SemiLat.cat

  TWO : SemiLat.Obj
  TWO = SemiLat.TWO

  scalar-comm : ∀ (f g : TWO ⇒ TWO) → (f ∘ g) ≈ (g ∘ f)
  scalar-comm f g .f≃f .eqfunc .eqfun O =
    begin
      fun f (fun g O)
    ≈⟨ resp-≃ f (⊥-preserving-≃ g) ⟩
      fun f O
    ≈⟨ ⊥-preserving-≃ f ⟩
      O
    ≈˘⟨ ⊥-preserving-≃ g ⟩
      fun g O
    ≈˘⟨ resp-≃ g (⊥-preserving-≃ f) ⟩
      fun g (fun f O)
    ∎ where open ≈-Reasoning two.isEquivalence
  scalar-comm f g .f≃f .eqfunc .eqfun I = go (fun f I) (fun g I) two.≃-refl two.≃-refl
    where
      open ≈-Reasoning two.isEquivalence

      step : ∀ (a b : Two) → a two.≃ fun f I → b two.≃ fun g I → fun f b two.≃ fun g a
      step O O _     _     = begin fun f O ≈⟨ ⊥-preserving-≃ f ⟩ O ≈˘⟨ ⊥-preserving-≃ g ⟩ fun g O ∎
      step O I eq-a  _     = begin fun f I ≈˘⟨ eq-a ⟩ O ≈˘⟨ ⊥-preserving-≃ g ⟩ fun g O ∎
      step I O _     eq-b  = begin fun f O ≈⟨ ⊥-preserving-≃ f ⟩ O ≈⟨ eq-b ⟩ fun g I ∎
      step I I eq-a  eq-b  = begin fun f I ≈˘⟨ eq-a ⟩ I ≈⟨ eq-b ⟩ fun g I ∎

      go : ∀ (a b : Two) → a two.≃ fun f I → b two.≃ fun g I → fun f (fun g I) two.≃ fun g (fun f I)
      go a b eq-a eq-b =
        begin
          fun f (fun g I)
        ≈⟨ resp-≃ f (two.≃-sym eq-b) ⟩
          fun f b
        ≈⟨ step a b eq-a eq-b ⟩
          fun g a
        ≈⟨ resp-≃ g eq-a ⟩
          fun g (fun f I)
        ∎

  import matrix-rep
  open matrix-rep SemiLat.cmon-enriched
    (CMon.cmon+products→biproducts SemiLat.cmon-enriched SemiLat.products)
    (HasTerminal.witness SemiLat.terminal)
    (HasInitial.is-initial SemiLat.initial)
    (HasTerminal.is-terminal SemiLat.terminal)
    TWO
    scalar-comm
    public

  𝓕 : Functor cat SemiLat.cat
  𝓕 .fobj = X^
  𝓕 .fmor f = f
  𝓕 .fmor-cong f≈ = f≈
  𝓕 .fmor-id = ≈-refl
  𝓕 .fmor-comp _ _ = ≈-refl

  open import finite-product-functor using (preserve-chosen-terminal; preserve-chosen-products)
  private
    module SemiLat' = Category SemiLat.cat
  open SemiLat'.IsIso

  SemiLat-BP = CMon.cmon+products→biproducts SemiLat.cmon-enriched SemiLat.products
  SemiLat-products = biproducts→products _ SemiLat-BP

  𝓕-preserve-products : preserve-chosen-products 𝓕 products SemiLat-products
  𝓕-preserve-products {m} {n} .inverse = X^-split m n .Iso.bwd
  𝓕-preserve-products {m} {n} .f∘inverse≈id = X^-split m n .Iso.fwd∘bwd≈id
  𝓕-preserve-products {m} {n} .inverse∘f≈id = X^-split m n .Iso.bwd∘fwd≈id

  𝓕-preserve-terminal : preserve-chosen-terminal 𝓕 terminal SemiLat.terminal
  𝓕-preserve-terminal .inverse = SemiLat'.id _
  𝓕-preserve-terminal .f∘inverse≈id = HasTerminal.to-terminal-unique SemiLat.terminal _ _
  𝓕-preserve-terminal .inverse∘f≈id = HasTerminal.to-terminal-unique SemiLat.terminal _ _

  open Interpretation
    cat terminal products
    SemiLat.cat SemiLat.cmon-enriched SemiLat.limits SemiLat.terminal SemiLat-BP
    𝓕 𝓕-preserve-terminal (λ {X} {Y} → 𝓕-preserve-products {X} {Y})
    public

  -- Sanity check: witness the equivalence Mat(Two) ≃ MatRep(SemiLat, TWO) by instantiating matrix-embedding
  -- with the iso between Two and End(TWO).
  open CMon.CMonEnriched SemiLat.cmon-enriched using (_+m_; εm; +m-runit)

  -- scalar : Two → End(TWO) in SemiLat.
  scalar : Two → TWO ⇒ TWO
  scalar O = εm
  scalar I = id TWO

  scalar-cong : ∀ {a b} → a two.≃ b → scalar a ≈ scalar b
  scalar-cong {O} {O} _ = ≈-refl
  scalar-cong {O} {I} (_ , ())
  scalar-cong {I} {O} (() , _)
  scalar-cong {I} {I} _ = ≈-refl

  scalar-ε : scalar O ≈ εm
  scalar-ε = ≈-refl

  scalar-ι : scalar I ≈ id TWO
  scalar-ι = ≈-refl

  open import commutative-monoid using (CommutativeMonoid)
  private
    module homCM {x y} = CommutativeMonoid (CMon.CMonEnriched.homCM SemiLat.cmon-enriched x y)

  -- scalar preserves addition (⊔). The I+I case needs idempotence of SemiLat's +m on id.
  scalar-+ : ∀ {a b} → scalar (a two.⊔ b) ≈ scalar a +m scalar b
  scalar-+ {O} {O} = ≈-sym homCM.+-lunit
  scalar-+ {O} {I} = ≈-sym homCM.+-lunit
  scalar-+ {I} {O} = ≈-sym +m-runit
  scalar-+ {I} {I} = I-idem
    where
      I-idem : id TWO ≈ id TWO +m id TWO
      I-idem .f≃f .eqfunc .eqfun O = two.≤-refl {O} , two.≤-refl {O}
      I-idem .f≃f .eqfunc .eqfun I = two.≤-refl {I} , two.≤-refl {I}

  -- scalar preserves multiplication (⊓). Composition of scalars via SemiLat's ∘.
  scalar-· : ∀ {a b} → scalar (a two.⊓ b) ≈ scalar a ∘ scalar b
  scalar-· {O} {O} = ≈-sym (CMon.CMonEnriched.comp-bilinear-ε₁ SemiLat.cmon-enriched εm)
  scalar-· {O} {I} = ≈-sym (CMon.CMonEnriched.comp-bilinear-ε₁ SemiLat.cmon-enriched (id TWO))
  scalar-· {I} {O} = ≈-sym id-left
  scalar-· {I} {I} = ≈-sym id-left

  -- scalar-inv : End(TWO) → Two, extracting f(I). Since TWO endomorphisms preserve ⊥, they
  -- are determined by their value at I, which is either O (giving εm) or I (giving id TWO).
  scalar-inv : TWO ⇒ TWO → Two
  scalar-inv f = fun f I

  scalar-inv-cong : ∀ {f g : TWO ⇒ TWO} → f ≈ g → scalar-inv f two.≃ scalar-inv g
  scalar-inv-cong p = p .f≃f .eqfunc .eqfun I

  scalar-inv-scalar : ∀ a → scalar-inv (scalar a) two.≃ a
  scalar-inv-scalar O = two.≃-refl {O}
  scalar-inv-scalar I = two.≃-refl {I}

  -- Endomorphismof TWO is determined by f(I).
  scalar-scalar-inv : ∀ (f : TWO ⇒ TWO) → scalar (scalar-inv f) ≈ f
  scalar-scalar-inv f = go (fun f I) two.≃-refl
    where
      -- ⊥-preserving gives us O ≃ fun f O via the pair (O ≤ fun f O = tt, fun f O ≤ O).
      O≃fO : O two.≃ fun f O
      O≃fO = tt , ⊥-preserving-≃ f .proj₁
      -- Given a two.≃ fun f I, show scalar a ≈ f pointwise.
      go : (a : Two) → a two.≃ fun f I → scalar a ≈ f
      go O eq .f≃f .eqfunc .eqfun O = O≃fO
      go O eq .f≃f .eqfunc .eqfun I = eq
      go I eq .f≃f .eqfunc .eqfun O = O≃fO
      go I eq .f≃f .eqfunc .eqfun I = eq

  import matrix-embedding
  module Mat≃MatRep = matrix-embedding
    SemiLat.cmon-enriched
    (CMon.cmon+products→biproducts SemiLat.cmon-enriched SemiLat.products)
    (HasTerminal.witness SemiLat.terminal)
    (HasInitial.is-initial SemiLat.initial)
    (HasTerminal.is-terminal SemiLat.terminal)
    TWO
    two.semiring
    scalar scalar-cong scalar-ε scalar-ι
    (λ {a} {b} → scalar-+ {a} {b}) (λ {a} {b} → scalar-· {a} {b})
    scalar-inv scalar-inv-cong scalar-inv-scalar scalar-scalar-inv
