{-# OPTIONS --postfix-projections --prop --safe #-}

module ho-model where

open import Level using (Level; 0ℓ; suc)
open import categories using (Category; HasProducts; HasTerminal; HasInitial; IsTerminal; IsInitial; op-coproducts→products; op-initial→terminal; HasCoproducts)
open import product-category using (product; product-limit; product-products; product-terminal)
open import cmon-enriched
  using (CMonEnriched; product-cmon-enriched; op-cmon-enriched; Biproduct; biproducts→products)
open import functor using (HasLimits; op-colimit; limits→limits')
import meet-semilattice-category
import join-semilattice-category
import fam
import indexed-family
open Category using (opposite)

------------------------------------------------------------------------------
-- Construct Meet × Join^op

M×Jop : Category (suc 0ℓ) 0ℓ 0ℓ
M×Jop = product meet-semilattice-category.cat (opposite join-semilattice-category.cat)

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
    (op-colimit _ (join-semilattice-category.colimits (opposite 𝒮) _))

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
J×Jop = product join-semilattice-category.cat (opposite join-semilattice-category.cat)

J×Jop-cmon-enriched : CMonEnriched J×Jop
J×Jop-cmon-enriched =
  product-cmon-enriched
    join-semilattice-category.cmon-enriched
    (op-cmon-enriched join-semilattice-category.cmon-enriched)

J×Jop-limits : ∀ (𝒮 : Category 0ℓ 0ℓ 0ℓ) → HasLimits 𝒮 J×Jop
J×Jop-limits 𝒮 D =
  product-limit _ _ 𝒮 D
    (join-semilattice-category.limits 𝒮 _)
    (op-colimit _ (join-semilattice-category.colimits (opposite 𝒮) _))

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
  open CMon.CMonEnriched SemiLat.cmon-enriched using (_+m_; εm; +m-runit; comp-bilinear-ε₁; comp-bilinear-ε₂; comp-bilinear₁; comp-bilinear₂)
  open import commutative-monoid using (CommutativeMonoid)

  TWO : SemiLat.Obj
  TWO = SemiLat.TWO

  private
    module homCM {x y} = CommutativeMonoid (CMon.CMonEnriched.homCM SemiLat.cmon-enriched x y)

  -- Semiring isomorphism Two ↔ End(TWO) in SemiLat. Each End(TWO) preserves ⊥, so is determined by its value
  -- at I (either εm or id).
  module scalar where
    to : Two → TWO ⇒ TWO
    to O = εm
    to I = id TWO

    from : TWO ⇒ TWO → Two
    from f = fun f I

    to-cong : ∀ {a b} → a two.≃ b → to a ≈ to b
    to-cong {O} {O} _ = ≈-refl
    to-cong {O} {I} (_ , ())
    to-cong {I} {O} (() , _)
    to-cong {I} {I} _ = ≈-refl

    preserves-ε : to O ≈ εm
    preserves-ε = ≈-refl

    preserves-ι : to I ≈ id TWO
    preserves-ι = ≈-refl

    preserves-+ : ∀ {a b} → to (a two.⊔ b) ≈ to a +m to b
    preserves-+ {O} {O} = ≈-sym homCM.+-lunit
    preserves-+ {O} {I} = ≈-sym homCM.+-lunit
    preserves-+ {I} {O} = ≈-sym +m-runit
    preserves-+ {I} {I} = I-idem
      where
        I-idem : id TWO ≈ id TWO +m id TWO
        I-idem .f≃f .eqfunc .eqfun O = two.≤-refl {O} , two.≤-refl {O}
        I-idem .f≃f .eqfunc .eqfun I = two.≤-refl {I} , two.≤-refl {I}

    preserves-· : ∀ {a b} → to (a two.⊓ b) ≈ to a ∘ to b
    preserves-· {O} {O} = ≈-sym (comp-bilinear-ε₁ εm)
    preserves-· {O} {I} = ≈-sym (comp-bilinear-ε₁ (id TWO))
    preserves-· {I} {O} = ≈-sym id-left
    preserves-· {I} {I} = ≈-sym id-left

    from-cong : ∀ {f g : TWO ⇒ TWO} → f ≈ g → from f two.≃ from g
    from-cong p = p .f≃f .eqfunc .eqfun I

    from∘to : ∀ a → from (to a) two.≃ a
    from∘to O = two.≃-refl {O}
    from∘to I = two.≃-refl {I}

    -- End(TWO) is determined by f(I).
    to∘from : ∀ (f : TWO ⇒ TWO) → to (from f) ≈ f
    to∘from f .f≃f .eqfunc .eqfun O with fun f I
    ... | O = tt , ⊥-preserving-≃ f .proj₁
    ... | I = tt , ⊥-preserving-≃ f .proj₁
    to∘from f .f≃f .eqfunc .eqfun I with fun f I
    ... | O = two.≃-refl {O}
    ... | I = two.≃-refl {I}

    open import prop-setoid using () renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
    open import setoid-cat using (SetoidCat)
    open _⇒s_
    open _≈s_

    iso : Category.Iso (SetoidCat 0ℓ 0ℓ) two.Two-setoid (Category.hom-setoid SemiLat.cat TWO TWO)
    iso .Category.Iso.fwd .func = to
    iso .Category.Iso.fwd .func-resp-≈ = to-cong
    iso .Category.Iso.bwd .func = from
    iso .Category.Iso.bwd .func-resp-≈ = from-cong
    iso .Category.Iso.fwd∘bwd≈id .func-eq {f₁} {f₂} f₁≈f₂ = ≈-trans (to∘from f₁) f₁≈f₂
    iso .Category.Iso.bwd∘fwd≈id .func-eq {a₁} {a₂} a₁≈a₂ = two.≃-trans (from∘to a₁) a₁≈a₂

    open import commutative-monoid using (_=[_]>_)
    open import commutative-semiring using (CommutativeSemiring)
    open CommutativeSemiring two.semiring using (additive)
    open CMon.CMonEnriched

    cmon-hom : additive =[ iso .Category.Iso.fwd ]> homCM SemiLat.cmon-enriched TWO TWO
    cmon-hom ._=[_]>_.preserve-ε = preserves-ε
    cmon-hom ._=[_]>_.preserve-+ {a} {b} = preserves-+ {a} {b}

    comm : ∀ (f g : TWO ⇒ TWO) → (f ∘ g) ≈ (g ∘ f)
    comm f g =
      begin
        f ∘ g
      ≈˘⟨ ∘-cong (to∘from f) (to∘from g) ⟩
        to a ∘ to b
      ≈˘⟨ preserves-· {a} {b} ⟩
        to (a two.⊓ b)
      ≈⟨ to-cong (two.⊓-cmon .CommutativeMonoid.+-comm {a} {b}) ⟩
        to (b two.⊓ a)
      ≈⟨ preserves-· {b} {a} ⟩
        to b ∘ to a
      ≈⟨ ∘-cong (to∘from g) (to∘from f) ⟩
        g ∘ f
      ∎ where
        open ≈-Reasoning isEquiv
        a = from f
        b = from g

  import matrix-embedding
  module Mat≃MatRep = matrix-embedding
    SemiLat.cmon-enriched
    (CMon.cmon+products→biproducts SemiLat.cmon-enriched SemiLat.products)
    (HasTerminal.witness SemiLat.terminal)
    (HasInitial.is-initial SemiLat.initial)
    (HasTerminal.is-terminal SemiLat.terminal)
    TWO
    two.Two-setoid
    two.semiring
    scalar.iso
    scalar.cmon-hom
    scalar.preserves-ι
    (λ {a} {b} → scalar.preserves-· {a} {b})
  open Mat≃MatRep hiding (prod; p₁; p₂; pair; pair-cong; pair-p₁; pair-p₂; pair-ext; 𝓕; terminal; initial; 𝓕-preserve-terminal) public

  𝓕 : Functor cat SemiLat.cat
  𝓕 .fobj = X^
  𝓕 .fmor f = f
  𝓕 .fmor-cong f≈ = f≈
  𝓕 .fmor-id = ≈-refl
  𝓕 .fmor-comp _ _ = ≈-refl

  open import finite-product-functor using (preserve-chosen-terminal; preserve-chosen-products)
  open IsIso

  SemiLat-BP = CMon.cmon+products→biproducts SemiLat.cmon-enriched SemiLat.products
  SemiLat-products = biproducts→products _ SemiLat-BP

  module _ where
    open Biproduct
    open Mat using (biproduct)
    module P = HasProducts products

    𝓕-preserve-products : preserve-chosen-products 𝓕 products SemiLat-products
    𝓕-preserve-products {m} {n} .inverse =
      copair (SemiLat-BP (X^ m) (X^ n)) (F .fmor (in₁ (biproduct m n))) (F .fmor (in₂ (biproduct m n)))
    𝓕-preserve-products {m} {n} .f∘inverse≈id =
      begin
        pair BP {X^ (P.prod m n)} (𝓕 .fmor {P.prod m n} {m} (P.p₁ {m} {n})) (𝓕 .fmor {P.prod m n} {n} (P.p₂ {m} {n}))
        ∘ copair BP {X^ (P.prod m n)}
            (F .fmor {m} {P.prod m n} (in₁ (biproduct m n)))
            (F .fmor {n} {P.prod m n} (in₂ (biproduct m n)))
      ≈⟨ pair-natural BP _ _ _ ⟩
        pair BP
          (P.p₁ {m} {n} ∘ copair BP {X^ (P.prod m n)}
                            (F .fmor {m} {P.prod m n} (in₁ (biproduct m n)))
                            (F .fmor {n} {P.prod m n} (in₂ (biproduct m n))))
          (P.p₂ {m} {n} ∘ copair BP {X^ (P.prod m n)}
                            (F .fmor {m} {P.prod m n} (in₁ (biproduct m n)))
                            (F .fmor {n} {P.prod m n} (in₂ (biproduct m n))))
      ≈⟨ pair-cong BP {prod BP} reduce-p₁ reduce-p₂ ⟩
        pair BP (p₁ BP) (p₂ BP)
      ≈⟨ pair-ext0 BP ⟩
        id (prod BP)
      ∎ where
        BP = SemiLat-BP (X^ m) (X^ n)

        reduce-p₁ : (P.p₁ {m} {n} ∘ copair BP {X^ (P.prod m n)}
                                      (F .fmor {m} {P.prod m n} (in₁ (biproduct m n)))
                                      (F .fmor {n} {P.prod m n} (in₂ (biproduct m n)))) ≈ p₁ BP
        reduce-p₁ =
          begin
            P.p₁ {m} {n} ∘ copair BP {X^ (P.prod m n)}
              (F .fmor {m} {P.prod m n} (in₁ (biproduct m n)))
              (F .fmor {n} {P.prod m n} (in₂ (biproduct m n)))
          ≈⟨ comp-bilinear₂ _ _ _ ⟩
            (P.p₁ {m} {n} ∘ (F .fmor {m} {P.prod m n} (in₁ (biproduct m n)) ∘ p₁ BP)) +m
            (P.p₁ {m} {n} ∘ (F .fmor {n} {P.prod m n} (in₂ (biproduct m n)) ∘ p₂ BP))
          ≈⟨ homCM.+-cong (≈-sym (assoc _ _ _)) (≈-sym (assoc _ _ _)) ⟩
            ((P.p₁ {m} {n} ∘ F .fmor {m} {P.prod m n} (in₁ (biproduct m n))) ∘ p₁ BP) +m
            ((P.p₁ {m} {n} ∘ F .fmor {n} {P.prod m n} (in₂ (biproduct m n))) ∘ p₂ BP)
          ≈⟨ homCM.+-cong
               (∘-cong (≈-trans (≈-sym (F .fmor-comp {m} {P.prod m n} {m} (p₁ (biproduct m n)) (in₁ (biproduct m n))))
                       (≈-trans (F .fmor-cong (id-1 (biproduct m n))) (F .fmor-id {m}))) ≈-refl)
               (∘-cong (≈-trans (≈-sym (F .fmor-comp {n} {P.prod m n} {m} (p₁ (biproduct m n)) (in₂ (biproduct m n))))
                       (≈-trans (F .fmor-cong (zero-1 (biproduct m n))) (Mat≃MatRep.F-εₘ {m} {n}))) ≈-refl) ⟩
            (id (X^ m) ∘ p₁ BP) +m (εm {X^ n} {X^ m} ∘ p₂ BP)
          ≈⟨ homCM.+-cong id-left (comp-bilinear-ε₁ _) ⟩
            p₁ BP +m εm
          ≈⟨ +m-runit ⟩
            p₁ BP
          ∎ where open ≈-Reasoning isEquiv

        reduce-p₂ : (P.p₂ {m} {n} ∘ copair BP {X^ (P.prod m n)}
                                      (F .fmor {m} {P.prod m n} (in₁ (biproduct m n)))
                                      (F .fmor {n} {P.prod m n} (in₂ (biproduct m n)))) ≈ p₂ BP
        reduce-p₂ =
          begin
            P.p₂ {m} {n} ∘ copair BP {X^ (P.prod m n)}
              (F .fmor {m} {P.prod m n} (in₁ (biproduct m n)))
              (F .fmor {n} {P.prod m n} (in₂ (biproduct m n)))
          ≈⟨ comp-bilinear₂ _ _ _ ⟩
            (P.p₂ {m} {n} ∘ (F .fmor {m} {P.prod m n} (in₁ (biproduct m n)) ∘ p₁ BP)) +m
            (P.p₂ {m} {n} ∘ (F .fmor {n} {P.prod m n} (in₂ (biproduct m n)) ∘ p₂ BP))
          ≈⟨ homCM.+-cong (≈-sym (assoc _ _ _)) (≈-sym (assoc _ _ _)) ⟩
            ((P.p₂ {m} {n} ∘ F .fmor {m} {P.prod m n} (in₁ (biproduct m n))) ∘ p₁ BP) +m
            ((P.p₂ {m} {n} ∘ F .fmor {n} {P.prod m n} (in₂ (biproduct m n))) ∘ p₂ BP)
          ≈⟨ homCM.+-cong
               (∘-cong (≈-trans (≈-sym (F .fmor-comp {m} {P.prod m n} {n} (p₂ (biproduct m n)) (in₁ (biproduct m n))))
                       (≈-trans (F .fmor-cong (zero-2 (biproduct m n))) (Mat≃MatRep.F-εₘ {n} {m}))) ≈-refl)
               (∘-cong (≈-trans (≈-sym (F .fmor-comp {n} {P.prod m n} {n} (p₂ (biproduct m n)) (in₂ (biproduct m n))))
                       (≈-trans (F .fmor-cong (id-2 (biproduct m n))) (F .fmor-id {n}))) ≈-refl) ⟩
            (εm {X^ m} {X^ n} ∘ p₁ BP) +m (id (X^ n) ∘ p₂ BP)
          ≈⟨ homCM.+-cong (comp-bilinear-ε₁ _) id-left ⟩
            εm +m p₂ BP
          ≈⟨ homCM.+-lunit ⟩
            p₂ BP
          ∎ where open ≈-Reasoning isEquiv

        open ≈-Reasoning isEquiv
    𝓕-preserve-products {m} {n} .inverse∘f≈id =
      begin
        copair BP {X^ (P.prod m n)}
          (F .fmor {m} {P.prod m n} (in₁ (biproduct m n)))
          (F .fmor {n} {P.prod m n} (in₂ (biproduct m n)))
        ∘ pair BP {X^ (P.prod m n)}
            (𝓕 .fmor {P.prod m n} {m} (P.p₁ {m} {n}))
            (𝓕 .fmor {P.prod m n} {n} (P.p₂ {m} {n}))
      ≈⟨ comp-bilinear₂ _ _ _ ⟩
        (copair BP {X^ (P.prod m n)}
           (F .fmor {m} {P.prod m n} (in₁ (biproduct m n)))
           (F .fmor {n} {P.prod m n} (in₂ (biproduct m n))) ∘
         (in₁ BP ∘ P.p₁ {m} {n})) +m
        (copair BP {X^ (P.prod m n)}
           (F .fmor {m} {P.prod m n} (in₁ (biproduct m n)))
           (F .fmor {n} {P.prod m n} (in₂ (biproduct m n))) ∘
         (in₂ BP ∘ P.p₂ {m} {n}))
      ≈⟨ homCM.+-cong (≈-sym (assoc _ _ _)) (≈-sym (assoc _ _ _)) ⟩
        ((copair BP {X^ (P.prod m n)}
            (F .fmor {m} {P.prod m n} (in₁ (biproduct m n)))
            (F .fmor {n} {P.prod m n} (in₂ (biproduct m n))) ∘ in₁ BP) ∘ P.p₁ {m} {n}) +m
        ((copair BP {X^ (P.prod m n)}
            (F .fmor {m} {P.prod m n} (in₁ (biproduct m n)))
            (F .fmor {n} {P.prod m n} (in₂ (biproduct m n))) ∘ in₂ BP) ∘ P.p₂ {m} {n})
      ≈⟨ homCM.+-cong (∘-cong (copair-in₁ BP _ _) ≈-refl) (∘-cong (copair-in₂ BP _ _) ≈-refl) ⟩
        (F .fmor {m} {P.prod m n} (in₁ (biproduct m n)) ∘ P.p₁ {m} {n}) +m
        (F .fmor {n} {P.prod m n} (in₂ (biproduct m n)) ∘ P.p₂ {m} {n})
      ≈⟨ homCM.+-cong
           (≈-sym (F .fmor-comp {P.prod m n} {m} {P.prod m n} (in₁ (biproduct m n)) (p₁ (biproduct m n))))
           (≈-sym (F .fmor-comp {P.prod m n} {n} {P.prod m n} (in₂ (biproduct m n)) (p₂ (biproduct m n)))) ⟩
        F .fmor {P.prod m n} {P.prod m n} (in₁ (biproduct m n) Mat.∘ p₁ (biproduct m n)) +m
        F .fmor {P.prod m n} {P.prod m n} (in₂ (biproduct m n) Mat.∘ p₂ (biproduct m n))
      ≈⟨ ≈-sym (Mat≃MatRep.F-+ₘ {P.prod m n} {P.prod m n}
                  (in₁ (biproduct m n) Mat.∘ p₁ (biproduct m n))
                  (in₂ (biproduct m n) Mat.∘ p₂ (biproduct m n))) ⟩
        F .fmor {P.prod m n} {P.prod m n}
          ((in₁ (biproduct m n) Mat.∘ p₁ (biproduct m n)) Mat.+ₘ
           (in₂ (biproduct m n) Mat.∘ p₂ (biproduct m n)))
      ≈⟨ F .fmor-cong (id-+ (biproduct m n)) ⟩
        F .fmor {P.prod m n} {P.prod m n} (Mat.I {P.prod m n})
      ≈⟨ F .fmor-id {P.prod m n} ⟩
        id (X^ (P.prod m n))
      ∎ where
        BP = SemiLat-BP (X^ m) (X^ n)
        open ≈-Reasoning isEquiv

  terminal : HasTerminal cat
  terminal .HasTerminal.witness = 0
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal =
    HasTerminal.to-terminal SemiLat.terminal
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext f =
    HasTerminal.to-terminal-ext SemiLat.terminal f

  initial : HasInitial cat
  initial .HasInitial.witness = 0
  initial .HasInitial.is-initial .IsInitial.from-initial =
    HasInitial.from-initial SemiLat.initial
  initial .HasInitial.is-initial .IsInitial.from-initial-ext f =
    HasInitial.from-initial-ext SemiLat.initial f

  𝓕-preserve-terminal : preserve-chosen-terminal 𝓕 terminal SemiLat.terminal
  𝓕-preserve-terminal .inverse = id _
  𝓕-preserve-terminal .f∘inverse≈id = HasTerminal.to-terminal-unique SemiLat.terminal _ _
  𝓕-preserve-terminal .inverse∘f≈id = HasTerminal.to-terminal-unique SemiLat.terminal _ _

  open Interpretation
    cat terminal products
    SemiLat.cat SemiLat.cmon-enriched SemiLat.limits SemiLat.terminal SemiLat-BP
    𝓕 𝓕-preserve-terminal (λ {X} {Y} → 𝓕-preserve-products {X} {Y})
    public
