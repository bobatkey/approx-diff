{-# OPTIONS --postfix-projections --prop --safe #-}

module jacobian where

open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_)
open import two using (Two; I; O; _⊓_; _⊔_; ⊔-upper₂; ≤-isPreorder)
open import basics using (IsPreorder)
open IsPreorder ≤-isPreorder using (_≃_; ≃-refl; ≃-trans)
import join-semilattice-category

open join-semilattice-category using (Obj; TWO; products; terminal)
open import categories using (HasProducts; HasTerminal)

-- Objects: Bool^n, the n-fold product of TWO in the category of join-semilattices.

private
  module P = HasProducts products
  module T = HasTerminal terminal

Bool^ : ℕ → Obj
Bool^ zero = T.witness
Bool^ (suc n) = P.prod TWO (Bool^ n)

open Obj hiding (_≃_; ≃-refl; ≃-sym; ≃-trans)

-- Standard basis vectors e_i: I at position i, O everywhere else.
e : ∀ {n} → Fin n → Bool^ n .Carrier
e {suc n} zero = I , Bool^ n .⊥
e {suc n} (suc i) = O , e i

proj : ∀ {n} → Fin n → Bool^ n .Carrier → Two
proj zero (b , _)  = b
proj (suc i) (_ , v) = proj i v

open import Data.Unit using (tt)
open import prop using (tt; _,_; _∧_; proj₁; proj₂)

-- Bool^n representation of a function.
tabulate : ∀ {n} → (Fin n → Two) → Bool^ n .Carrier
tabulate {zero} _ = tt
tabulate {suc n} f = f zero , tabulate {n} (λ i → f (suc i))

-- Dot product of two Bool^n, i.e. whether there exists a position where both are I.
module _ where
  _⋅_ : ∀ {n} → Bool^ n .Carrier → Bool^ n .Carrier → Two
  _⋅_ {zero}  _ _ = O
  _⋅_ {suc n} (a , u) (b , v) = (a ⊓ b) ⊔ _⋅_ {n} u v

  -- Dot is linear and monotone in its second argument.

  ⋅-⊥ : ∀ {n} (u : Bool^ n .Carrier) → two._≤_ (_⋅_ {n} u (Bool^ n .⊥)) O
  ⋅-⊥ {zero}  _ = tt
  ⋅-⊥ {suc n} (O , v) = ⋅-⊥ {n} v
  ⋅-⊥ {suc n} (I , v) = ⋅-⊥ {n} v

  ⋅-∨ : ∀ {n} (u v w : Bool^ n .Carrier)
      → two._≤_ (_⋅_ {n} u (Bool^ n ._∨_ v w)) ((_⋅_ {n} u v) ⊔ (_⋅_ {n} u w))
  ⋅-∨ {zero} _ _ _ = tt
  ⋅-∨ {suc n} (O , u) (_ , v) (_ , w) = ⋅-∨ {n} u v w
  ⋅-∨ {suc n} (I , u) (O , v) (O , w) = ⋅-∨ {n} u v w
  ⋅-∨ {suc n} (I , u) (O , v) (I , w) = ⊔-upper₂
  ⋅-∨ {suc n} (I , u) (I , v) (_ , w) = tt

  ⋅-mono : ∀ {n} (u : Bool^ n .Carrier) {v w : Bool^ n .Carrier}
         → Bool^ n ._≤_ v w → two._≤_ (_⋅_ {n} u v) (_⋅_ {n} u w)
  ⋅-mono {zero}  _ _ = tt
  ⋅-mono {suc n} (O , u) {_ , v} {_ , w} (_ , v≤w) = ⋅-mono {n} u v≤w
  ⋅-mono {suc n} (I , u) {O , v} {_ , w} (_   , v≤w) = two.≤-trans (⋅-mono {n} u v≤w) ⊔-upper₂
  ⋅-mono {suc n} (I , u) {I , v} {I , w} (_   , v≤w) = tt

_⇒J_ : ℕ → ℕ → Set
m ⇒J n = Bool^ m ⇒ Bool^ n
  where open join-semilattice-category using (_⇒_)

-- Transpose f^T : Bool^n ⇒ Bool^m, defined by f^T(v)_i = f(e_i) ⋅ v.
module _ where
  open join-semilattice-category using (_⇒_)
  open join-semilattice-category._⇒_
  import join-semilattice
  open join-semilattice._=>_
  open import preorder using (_=>_)
  open preorder._=>_

  private
    -- Bool^m is isomorphic to Fin m → Two, witnessed by tabulate and project. We only need the tabulate
    -- direction here.
    tabulate-mono : ∀ {m} (g h : Fin m → Two)
               → (∀ i → two._≤_ (g i) (h i))
               → Bool^ m ._≤_ (tabulate {m} g) (tabulate {m} h)
    tabulate-mono {zero}  g h p = tt
    tabulate-mono {suc m} g h p = p zero , tabulate-mono {m} _ _ (λ i → p (suc i))

    tabulate-⊥ : ∀ {m} → Bool^ m ._≤_ (tabulate {m} (λ _ → O)) (Bool^ m .⊥)
    tabulate-⊥ {zero}  = tt
    tabulate-⊥ {suc m} = tt , tabulate-⊥ {m}

    tabulate-∨ : ∀ {m} (g h : Fin m → Two) →
                 Bool^ m ._≤_ (tabulate {m} (λ i → g i ⊔ h i)) (Bool^ m ._∨_ (tabulate {m} g) (tabulate {m} h))
    tabulate-∨ {zero}  g h = tt
    tabulate-∨ {suc m} g h = two.≤-refl , tabulate-∨ {m} (λ i → g (suc i)) (λ i → h (suc i))

    proj-tabulate : ∀ {n} (g : Fin n → Two) (i : Fin n) → proj i (tabulate {n} g) ≃ g i
    proj-tabulate {suc n} g zero = ≃-refl
    proj-tabulate {suc n} g (suc i) = proj-tabulate {n} (λ i → g (suc i)) i

-- Morphisms: join-semilattice morphisms Bool^m → Bool^n.
  transpose : ∀ {m n} → m ⇒J n → n ⇒J m
  transpose {m} {n} f .*→* .func .fun v = tabulate {m} (λ i → _⋅_ {n} (f .fun (e i)) v)
  transpose {m} {n} f .*→* .func .mono v≤w = tabulate-mono {m} _ _ (λ i → ⋅-mono {n} (f .fun (e i)) v≤w)
  transpose {m} {n} f .*→* .∨-preserving {v} {w} =
    Bool^ m .≤-trans (tabulate-mono {m} _ _ (λ i → ⋅-∨ {n} (f .fun (e i)) v w))
                     (tabulate-∨ {m} _ _)
  transpose {m} {n} f .*→* .⊥-preserving =
    Bool^ m .≤-trans (tabulate-mono {m} _ _ (λ i → ⋅-⊥ {n} (f .fun (e i))))
                     (tabulate-⊥ {m})

  -- Sanity-check that this is actually matrix transposition.
  private
    -- Every join-preserving map between Bool vectors is Bool-linear (determined by its values on basis vectors),
    -- so equivalent to an n×m Bool matrix.
    matrix : ∀ {m n} → m ⇒J n → Fin n → Fin m → Two
    matrix f j i = proj j (f .fun (e i))

    ⋅-e : ∀ {n} (u : Bool^ n .Carrier) (j : Fin n) → _⋅_ {n} u (e j) ≃ proj j u
    ⋅-e {suc n} (O , u) zero = ⋅-⊥ {n} u , tt
    ⋅-e {suc n} (I , u) zero = tt , tt
    ⋅-e {suc n} (O , u) (suc j) = ⋅-e {n} u j
    ⋅-e {suc n} (I , u) (suc j) = ⋅-e {n} u j

    transpose-matrix : ∀ m n (f : m ⇒J n) (i : Fin m) (j : Fin n) →
                      matrix {n} {m} (transpose {m} {n} f) i j ≃ matrix {m} {n} f j i
    transpose-matrix m n f i j =
      ≃-trans (proj-tabulate {m} (λ k → _⋅_ {n} (f .fun (e k)) (e j)) i)
              (⋅-e {n} (f .fun (e i)) j)
