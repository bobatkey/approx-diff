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
  open import two using (Two; O; I)
  open import matrix two.semiring public

  import join-semilattice-category as SemiLat
  open SemiLat using (Obj; _⇒_; _≃m_)
  open Obj
  open _⇒_
  open _≃m_
  open import join-semilattice using (JoinSemilattice; _=>_)
  open JoinSemilattice
  open _=>_
  open join-semilattice._≃m_ using (eqfunc)
  open import preorder using (Preorder)
  open Preorder
  open preorder._=>_ using (fun; mono)
  open preorder._≃m_ using (eqfun)
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Fin using (Fin; zero; suc)
  open import prop using (tt; _,_)
  open import basics using (IsPreorder; IsJoin; IsBottom; IsMeet)

  -- 𝓕(n): the pointwise join-semilattice on Vec n = Fin n → Two.
  𝓕-obj : ℕ → Obj
  𝓕-obj n .carrier .Carrier = Vec n
  𝓕-obj n .carrier ._≤_ u v = ∀ i → two._≤_ (u i) (v i)
  𝓕-obj n .carrier .≤-isPreorder .IsPreorder.refl i = two.≤-refl
  𝓕-obj n .carrier .≤-isPreorder .IsPreorder.trans p q i = two.≤-trans (p i) (q i)
  𝓕-obj n .joins ._∨_ u v i = two._⊔_ (u i) (v i)
  𝓕-obj n .joins .⊥ _ = O
  𝓕-obj n .joins .∨-isJoin .IsJoin.inl i = two.⊔-upper₁
  𝓕-obj n .joins .∨-isJoin .IsJoin.inr i = two.⊔-upper₂
  𝓕-obj n .joins .∨-isJoin .IsJoin.[_,_] p q i = two.⊔-least (p i) (q i)
  𝓕-obj n .joins .⊥-isBottom .IsBottom.≤-bottom _ = tt

  -- 𝓕 on morphisms: matrix-vector multiplication.
  𝓕-mor : ∀ {m n} → Mat n m → 𝓕-obj m ⇒ 𝓕-obj n
  𝓕-mor M .*→* .func .fun v i = Σ (λ j → two._⊓_ (M i j) (v j))
  𝓕-mor M .*→* .func .mono v≤w i =
    +-to-Σ.Σ-preserves two._≤_ two.≤-refl (IsJoin.mono two.⊔-isJoin)
      (λ j → IsMeet.mono two.⊓-isMeet two.≤-refl (v≤w j))
  𝓕-mor {m} M .*→* .∨-preserving {u} {v} i =
    two.≤-trans
      (+-to-Σ.Σ-preserves two._≤_ two.≤-refl (IsJoin.mono two.⊔-isJoin) {m}
        (λ j → prop.proj₁ (·-+-distribₗ {M i j} {u j} {v j})))
      (prop.proj₂ (Σ-+ {m} (λ j → M i j two.⊓ u j) (λ j → M i j two.⊓ v j)))
  𝓕-mor {m} M .*→* .⊥-preserving i =
    prop.proj₁ (two.≃-trans (Σ-cong {m} (λ j → ε-annihilᵣ)) (Σ-ε {m}))

  open import functor using (Functor)
  open Functor

  𝓕 : Functor cat SemiLat.cat
  𝓕 .fobj = 𝓕-obj
  𝓕 .fmor = 𝓕-mor
  𝓕 .fmor-cong {x} p .f≃f .eqfunc .eqfun v =
    (λ i → prop.proj₁ (Σ-cong {x} (λ j → IsMeet.cong two.⊓-isMeet (p i j) (two.≃-refl {v j})))) ,
    (λ i → prop.proj₂ (Σ-cong {x} (λ j → IsMeet.cong two.⊓-isMeet (p i j) (two.≃-refl {v j}))))
  𝓕 .fmor-id {x} .f≃f .eqfunc .eqfun v =
    (λ i → prop.proj₁ (Σ-unit {x} i v)) , (λ i → prop.proj₂ (Σ-unit {x} i v))
  𝓕 .fmor-comp {x} {y} f g .f≃f .eqfunc .eqfun v =
    (λ i → prop.proj₁ (chain i)) , (λ i → prop.proj₂ (chain i))
    where
      chain : ∀ i → two._≃_
        (Σ {x} (λ j → Σ {y} (λ k → two._⊓_ (f i k) (g k j)) two.⊓ v j))
        (Σ {y} (λ k → f i k two.⊓ Σ {x} (λ j → g k j two.⊓ v j)))
      chain i =
        two.≃-trans (Σ-cong {x} (λ j → Σ-·-distribᵣ (λ k → f i k two.⊓ g k j) (v j)))
          (two.≃-trans (Σ-cong {x} (λ j → Σ-cong {y} (λ k → ·-assoc {f i k} {g k j} {v j})))
            (two.≃-trans (Σ-interchange {x} {y} (λ j k → f i k two.⊓ (g k j two.⊓ v j)))
              (Σ-cong {y} (λ k → two.≃-sym (Σ-·-distribₗ (f i k) (λ j → g k j two.⊓ v j))))))

  open import finite-product-functor using (preserve-chosen-terminal; preserve-chosen-products)
  open import cmon-enriched using (biproducts→products)

  open Category SemiLat.cat using (IsIso) renaming (_∘_ to _∘ₛ_; id to idₛ)
  open IsIso

  SemiLat-BP = cmon-enriched.cmon+products→biproducts SemiLat.cmon-enriched SemiLat.products

  𝓕-preserve-terminal : preserve-chosen-terminal 𝓕 terminal SemiLat.terminal
  𝓕-preserve-terminal .inverse .*→* .func .fun _ _ = O
  𝓕-preserve-terminal .inverse .*→* .func .mono _ ()
  𝓕-preserve-terminal .inverse .*→* .∨-preserving ()
  𝓕-preserve-terminal .inverse .*→* .⊥-preserving ()
  𝓕-preserve-terminal .f∘inverse≈id = HasTerminal.to-terminal-unique SemiLat.terminal _ _
  𝓕-preserve-terminal .inverse∘f≈id .f≃f .eqfunc .eqfun v = (λ ()) , (λ ())

  SemiLat-products = biproducts→products SemiLat.cmon-enriched SemiLat-BP
  open HasProducts SemiLat-products using (pair)
  Mat-products = biproducts→products cmon biproduct

  open import Data.Nat using () renaming (_+_ to _+ℕ_)

  inv : ∀ {x y} → HasProducts.prod SemiLat-products (𝓕-obj x) (𝓕-obj y) ⇒ 𝓕-obj (x +ℕ y)
  inv {x} {y} .*→* .func .fun uv i = concat {x} {y} (proj₁ uv) (proj₂ uv) i
  inv {x} .*→* .func .mono (p , q) = concat-preserves {x} two._≤_ p q
  inv {x} .*→* .∨-preserving {uv} {uv'} i =
    prop.proj₁ (concat-+ {x} (proj₁ uv) (proj₁ uv') (proj₂ uv) (proj₂ uv') i)
  inv {x} .*→* .⊥-preserving i = prop.proj₁ (concat-ε {x} i)

  split-concat : ∀ {x y} → pair (𝓕-mor (p₁ {x} {y})) (𝓕-mor (p₂ {x} {y})) ∘ₛ inv {x} {y} ≃m idₛ _
  split-concat .f≃f .eqfunc .eqfun uv = {!!}

  concat-split : ∀ {x y} → inv {x} {y} ∘ₛ pair (𝓕-mor (p₁ {x} {y})) (𝓕-mor (p₂ {x} {y})) ≃m idₛ _
  concat-split = {!!}

  𝓕-preserve-products : preserve-chosen-products 𝓕 Mat-products SemiLat-products
  𝓕-preserve-products .inverse = inv
  𝓕-preserve-products .f∘inverse≈id = split-concat
  𝓕-preserve-products .inverse∘f≈id = concat-split

  open Interpretation
    cat terminal Mat-products
    SemiLat.cat SemiLat.cmon-enriched SemiLat.limits SemiLat.terminal SemiLat-BP
    𝓕 𝓕-preserve-terminal (λ {X} {Y} → 𝓕-preserve-products {X} {Y})
    public
