{-# OPTIONS --postfix-projections --prop --safe #-}

module ho-model where

open import Level using (Level; 0ℓ; suc)
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

open import functor using (Functor)
open import Data.Product using (_,_; proj₁; proj₂)
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

  𝓕 : Functor galois.cat M×Jop
  𝓕 .fobj X =
    record { carrier = X .galois.Obj.carrier ; meets = X .galois.Obj.meets } ,
    record { carrier = X .galois.Obj.carrier ; joins = X .galois.Obj.joins }
  𝓕 .fmor f =
    record { *→* = galois._⇒g_.right-∧ f } ,
    record { *→* = galois._⇒g_.left-∨ f }
  𝓕 .fmor-cong f≃g =
    record { f≃f = record { eqfunc = f≃g .galois._≃g_.right-eq } } ,
    record { f≃f = record { eqfunc = f≃g .galois._≃g_.left-eq } }
  𝓕 .fmor-id {X} =
    record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } } ,
    record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } }
  𝓕 .fmor-comp f g =
    (record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } }) ,
    (record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } })

  private
    module M×Jop' = Category M×Jop

  open M×Jop'.IsIso

  𝓕-preserve-terminal : preserve-chosen-terminal 𝓕 galois.terminal M×Jop-terminal
  𝓕-preserve-terminal .inverse =
    record { *→* = meet-semilattice.terminal } ,
    record { *→* = join-semilattice.initial }
  𝓕-preserve-terminal .f∘inverse≈id =
    HasTerminal.to-terminal-unique M×Jop-terminal _ _
  𝓕-preserve-terminal .inverse∘f≈id =
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

  𝓕 : Functor conjugate.cat J×Jop
  𝓕 .fobj X =
    record { carrier = X .conjugate.Obj.carrier ; joins = X .conjugate.Obj.joins } ,
    record { carrier = X .conjugate.Obj.carrier ; joins = X .conjugate.Obj.joins }
  𝓕 .fmor f =
    record { *→* = conjugate._⇒c_.right-∨ f } ,
    record { *→* = conjugate._⇒c_.left-∨ f }
  𝓕 .fmor-cong f≃g =
    record { f≃f = record { eqfunc = f≃g .conjugate._≃c_.right-eq } } ,
    record { f≃f = record { eqfunc = f≃g .conjugate._≃c_.left-eq } }
  𝓕 .fmor-id {X} =
    record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } } ,
    record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } }
  𝓕 .fmor-comp f g =
    (record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } }) ,
    (record { f≃f = record { eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl } })

  private
    module J×Jop' = Category J×Jop

  open J×Jop'.IsIso

  𝓕-preserve-terminal : preserve-chosen-terminal 𝓕 conjugate.terminal J×Jop-terminal
  𝓕-preserve-terminal .inverse =
    record { *→* = join-semilattice.terminal } ,
    record { *→* = join-semilattice.initial }
  𝓕-preserve-terminal .f∘inverse≈id =
    HasTerminal.to-terminal-unique J×Jop-terminal _ _
  𝓕-preserve-terminal .inverse∘f≈id =
    record { f≃f = record { eqfunc = record { eqfun = λ x → tt , tt } } } ,
    record { f≃f = record { eqfunc = record { eqfun = λ x → tt , tt } } }

  open join-semilattice-category._⇒_
  open join-semilattice-category._≃m_
  open join-semilattice._≃m_
  open preorder._≃m_
  open conjugate.Obj

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

  import matrices
  open matrices SemiLat.cmon-enriched
    (CMon.cmon+products→biproducts SemiLat.cmon-enriched SemiLat.products)
    (categories.HasTerminal.witness SemiLat.terminal)
    (categories.HasInitial.is-initial SemiLat.initial)
    (categories.HasTerminal.is-terminal SemiLat.terminal)
    TWO
    scalar-comm
    public

  𝓕 : Functor cat SemiLat.cat
  𝓕 .fobj = X^
  𝓕 .fmor f = f
  𝓕 .fmor-cong f≈ = f≈
  𝓕 .fmor-id = Category.≈-refl SemiLat.cat
  𝓕 .fmor-comp _ _ = Category.≈-refl SemiLat.cat

  open import finite-product-functor using (preserve-chosen-terminal)
  private
    module SemiLat' = Category SemiLat.cat
  open SemiLat'.IsIso

  open import finite-product-functor using (preserve-chosen-products)

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

  import conjugate
  open import Data.Nat using (ℕ; zero; suc)

  open import prop using (tt; _,_; proj₁; proj₂; _⇔_)
  import Data.Unit
  open import basics using (IsMeet; IsTop)
  import meet-semilattice
  open meet-semilattice.MeetSemilattice

  -- X^n as a conjugate.Obj (Heyting algebra): carrier and joins from Mat, meets by induction.
  module X^-Heyting where
    open SemiLat.Obj

    private
      meets : ∀ n → meet-semilattice.MeetSemilattice (carrier (X^ n))
      meets zero ._∧_ _ _ = Data.Unit.tt
      meets zero .⊤ = Data.Unit.tt
      meets zero .∧-isMeet .IsMeet.π₁ = tt
      meets zero .∧-isMeet .IsMeet.π₂ = tt
      meets zero .∧-isMeet .IsMeet.⟨_,_⟩ _ _ = tt
      meets zero .⊤-isTop .IsTop.≤-top = tt
      meets (suc n) ._∧_ (a , u) (b , v) = (a two.⊓ b) , meets n ._∧_ u v
      meets (suc n) .⊤ = (I , meets n .⊤)
      meets (suc n) .∧-isMeet .IsMeet.π₁ = two.⊓-isMeet .IsMeet.π₁ , meets n .∧-isMeet .IsMeet.π₁
      meets (suc n) .∧-isMeet .IsMeet.π₂ = two.⊓-isMeet .IsMeet.π₂ , meets n .∧-isMeet .IsMeet.π₂
      meets (suc n) .∧-isMeet .IsMeet.⟨_,_⟩ (a , u) (b , v) =
        two.⊓-isMeet .IsMeet.⟨_,_⟩ a b , meets n .∧-isMeet .IsMeet.⟨_,_⟩ u v
      meets (suc n) .⊤-isTop .IsTop.≤-top = two.I-isTop .IsTop.≤-top , meets n .⊤-isTop .IsTop.≤-top

    -- x # y = (x ∧ y) ≤ ⊥, using meets for ∧ and X^ for ≤ and ⊥.
    _#_ : ∀ {n} → Carrier (X^ n) → Carrier (X^ n) → Prop
    _#_ {n} x y = _≤_ (X^ n) (meets n ._∧_ x y) (⊥ (X^ n))

    #-reflect : ∀ n {x y} → (∀ z → _#_ {n} y z → _#_ {n} x z) → _≤_ (X^ n) x y
    #-reflect zero _ = tt
    #-reflect (suc n) {a , u} {b , v} h =
      conjugate.TWO .conjugate.Obj.#-reflect (λ c b#c → proj₁ (h (c , ⊥ (X^ n)) (b#c , meets n .∧-isMeet .IsMeet.π₂))) ,
      #-reflect n (λ w v#w → proj₂ (h (conjugate.TWO .conjugate.Obj.⊥ , w) (two.⊓-isMeet .IsMeet.π₂ , v#w)))

    ∧-∨-distrib : ∀ n x y z → _≤_ (X^ n)
                  (meets n ._∧_ x (_∨_ (X^ n) y z)) (_∨_ (X^ n) (meets n ._∧_ x y) (meets n ._∧_ x z))
    ∧-∨-distrib zero _ _ _ = tt
    ∧-∨-distrib (suc n) (a , u) (b , v) (c , w) =
      conjugate.TWO .conjugate.Obj.∧-∨-distrib a b c , ∧-∨-distrib n u v w

    ∨-∧-distrib : ∀ n x y z → _≤_ (X^ n) (_∨_ (X^ n) x (meets n ._∧_ y z))
                                    (meets n ._∧_ (_∨_ (X^ n) x y) (_∨_ (X^ n) x z))
    ∨-∧-distrib zero _ _ _ = tt
    ∨-∧-distrib (suc n) (a , u) (b , v) (c , w) =
      conjugate.TWO .conjugate.Obj.∨-∧-distrib a b c , ∨-∧-distrib n u v w

    conj : ℕ → conjugate.Obj
    conj n .conjugate.Obj.carrier = carrier (X^ n)
    conj n .conjugate.Obj.joins = joins (X^ n)
    conj n .conjugate.Obj.meets = meets n
    conj n .conjugate.Obj.#-reflect = #-reflect n
    conj n .conjugate.Obj.∧-∨-distrib = ∧-∨-distrib n
    conj n .conjugate.Obj.∨-∧-distrib = ∨-∧-distrib n

    -- Carrier-level negation on X^n (componentwise two.¬).
    ¬^ : ∀ {n} → Carrier (X^ n) → Carrier (X^ n)
    ¬^ {zero} _ = Data.Unit.tt
    ¬^ {suc n} (a , u) = two.¬ a , ¬^ {n} u

    ¬^-antitone : ∀ {n} {x y : Carrier (X^ n)} → _≤_ (X^ n) x y → _≤_ (X^ n) (¬^ {n} y) (¬^ {n} x)
    ¬^-antitone {zero} _ = tt
    ¬^-antitone {suc n} (a≤b , u≤v) = two.¬-antitone a≤b , ¬^-antitone {n} u≤v

  open X^-Heyting using () renaming (conj to X^-conj; ¬^ to X^-¬; ¬^-antitone to X^-¬-antitone)
  open conjugate using (_⇒c_)
  open _⇒c_

  open SemiLat._⇒_ renaming (*→* to *→*J)
  open join-semilattice._=>_ using (func)
  open preorder._=>_ using (fun)

  import galois
  open galois using (_⇒g_)
  open _⇒g_

  -- X^n as a galois.Obj: carrier and joins from Mat, meets from X^-conj.
  X^-gal : ℕ → galois.Obj
  X^-gal n .galois.Obj.carrier = SemiLat.Obj.carrier (X^ n)
  X^-gal n .galois.Obj.meets = conjugate.Obj.meets (X^-conj n)
  X^-gal n .galois.Obj.joins = SemiLat.Obj.joins (X^ n)

  -- Disjointness ↔ below complement.
  #-↔-≤ : ∀ {n} (x y : conjugate.Obj.Carrier (X^-conj n)) →
           conjugate.Obj._#_ (X^-conj n) x y ⇔ X^-conj n .conjugate.Obj._≤_ x (X^-¬ {n} y)
  #-↔-≤ x y .proj₁ = {!!}
  #-↔-≤ x y .proj₂ = {!!}

  -- Negation is involutive.
  ¬-involutive : ∀ {n} (x : conjugate.Obj.Carrier (X^-conj n)) →
                 conjugate.Obj._≃_ (X^-conj n) x (X^-¬ {n} (X^-¬ {n} x))
  ¬-involutive = {!!}

  -- The adjoint: ¬ ∘ transpose f ∘ ¬ (as a monotone map).
  adjoint : ∀ {m n} → X^ m ⇒ X^ n →
            preorder._=>_ (SemiLat.Obj.carrier (X^ n)) (SemiLat.Obj.carrier (X^ m))
  adjoint {m} {n} f .fun v = X^-¬ {m} (transpose {m} {n} f .*→*J .func .fun (X^-¬ {n} v))
  adjoint {m} {n} f .preorder._=>_.mono v≤w =
    X^-¬-antitone {m} (transpose {m} {n} f .*→*J .func .preorder._=>_.mono (X^-¬-antitone {n} v≤w))

  -- ¬(transpose f v) ≃ adjoint f (¬ v)
  ¬transpose≃adjoint¬ : ∀ {m n} (f : X^ m ⇒ X^ n) (v : galois.Obj.Carrier (X^-gal n)) →
                        galois.Obj._≃_ (X^-gal m) (X^-¬ {m} (transpose {m} {n} f .*→*J .func .fun v))
                                                  (adjoint {m} {n} f .fun (X^-¬ {n} v))
  ¬transpose≃adjoint¬ = {!!}

  -- (f, adjoint f) is a Galois connection (the main theorem).
  to-gal : ∀ {m n} → X^ m ⇒ X^ n → X^-gal n ⇒g X^-gal m
  to-gal {m} {n} f .right = adjoint {m} {n} f
  to-gal {m} {n} f .left = f .*→*J .func
  to-gal {m} {n} f .left⊣right {x} {y} .proj₁ = {!!}
  to-gal {m} {n} f .left⊣right {x} {y} .proj₂ = {!!}

  -- (transpose f, f) is a conjugate pair; derived from to-gal via De Morgan duality.
  to-conj : ∀ {m n} → X^ m ⇒ X^ n → X^-conj n ⇒c X^-conj m
  to-conj {m} {n} f .right = transpose {m} {n} f .*→*J .func
  to-conj {m} {n} f .left = f .*→*J .func
  to-conj {m} {n} f .conjugate {x} {y} .proj₁ = {!!}
  to-conj {m} {n} f .conjugate {x} {y} .proj₂ = {!!}
