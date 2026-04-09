{-# OPTIONS --postfix-projections --prop --safe #-}

module jacobian where

open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_)
open import two using (Two; I; O; _⊓_; _⊔_; ⊔-upper₂)
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

open Obj

-- Standard basis vectors e_i: I at position i, O everywhere else.
e : ∀ {n} → Fin n → Bool^ n .Carrier
e {suc n} zero = I , Bool^ n .⊥
e {suc n} (suc i) = O , e i

-- Morphisms: join-semilattice morphisms Bool^m → Bool^n.
-- Every such map is Bool-linear (determined by its values on basis vectors), so equivalent to an n×m Bool matrix.
-- The transpose (giving the backward/J^op component) will be derived.

proj : ∀ {n} → Fin n → Bool^ n .Carrier → Two
proj zero (b , _)  = b
proj (suc i) (_ , v) = proj i v

open import Data.Unit using (tt)
open import prop using (tt; _,_; _∧_)

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
    tabulate-⋅-⊥ : ∀ {m} {n} (g : Fin m → Bool^ n .Carrier) →
                   Bool^ m ._≤_ (tabulate {m} (λ i → _⋅_ {n} (g i) (Bool^ n .⊥))) (Bool^ m .⊥)
    tabulate-⋅-⊥ {zero} {n} g = tt
    tabulate-⋅-⊥ {suc m} {n} g = ⋅-⊥ {n} (g zero) , tabulate-⋅-⊥ {m} {n} (λ i → g (suc i))

    tabulate-⋅-∨ : ∀ {m} {n} (g : Fin m → Bool^ n .Carrier) (v w : Bool^ n .Carrier) →
                   Bool^ m ._≤_ (tabulate {m} (λ i → _⋅_ {n} (g i) (Bool^ n ._∨_ v w)))
                                (Bool^ m ._∨_ (tabulate {m} (λ i → _⋅_ {n} (g i) v)) (tabulate {m} (λ i → _⋅_ {n} (g i) w)))
    tabulate-⋅-∨ {zero} {n} g v w = tt
    tabulate-⋅-∨ {suc m} {n} g v w = ⋅-∨ {n} (g zero) v w , tabulate-⋅-∨ {m} {n} (λ i → g (suc i)) v w

    tabulate-⋅-mono : ∀ {m} {n} (g : Fin m → Bool^ n .Carrier) {v w : Bool^ n .Carrier}
                    → Bool^ n ._≤_ v w
                    → Bool^ m ._≤_ (tabulate {m} (λ i → _⋅_ {n} (g i) v)) (tabulate {m} (λ i → _⋅_ {n} (g i) w))
    tabulate-⋅-mono {zero}  {n} g v≤w = tt
    tabulate-⋅-mono {suc m} {n} g v≤w = ⋅-mono {n} (g zero) v≤w , tabulate-⋅-mono {m} {n} (λ i → g (suc i)) v≤w

  transpose : ∀ {m n} → m ⇒J n → n ⇒J m
  transpose {m} {n} f .*→* .func .fun v = tabulate {m} (λ i → _⋅_ {n} (f .fun (e i)) v)
  transpose {m} {n} f .*→* .func .mono v≤w = tabulate-⋅-mono {m} {n} (λ i → f .fun (e i)) v≤w
  transpose {m} {n} f .*→* .∨-preserving {v} {w} = tabulate-⋅-∨ {m} {n} (λ i → f .fun (e i)) v w
  transpose {m} {n} f .*→* .⊥-preserving = tabulate-⋅-⊥ {m} {n} (λ i → f .fun (e i))

  -- Sanity-check that this is actually matrix transposition.
  open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

  matrix : ∀ {m n} → m ⇒J n → Fin n → Fin m → Two
  matrix f j i = proj j (f .fun (e i))

  proj-tabulate : ∀ {n} (g : Fin n → Two) (i : Fin n) → proj i (tabulate {n} g) ≡ g i
  proj-tabulate {suc n} g zero = ≡-refl
  proj-tabulate {suc n} g (suc i) = proj-tabulate {n} (λ i → g (suc i)) i

  ⋅-e : ∀ {n} (u : Bool^ n .Carrier) (j : Fin n)
      → two._≤_ (_⋅_ {n} u (e j)) (proj j u) ∧ two._≤_ (proj j u) (_⋅_ {n} u (e j))
  ⋅-e {suc n} (O , u) zero = ⋅-⊥ {n} u , tt
  ⋅-e {suc n} (I , u) zero = tt , tt
  ⋅-e {suc n} (O , u) (suc j) = ⋅-e {n} u j
  ⋅-e {suc n} (I , u) (suc j) = ⋅-e {n} u j

  transpose-matrix : ∀ m n (f : m ⇒J n) (i : Fin m) (j : Fin n)
                   → two._≤_ (matrix {n} {m} (transpose {m} {n} f) i j) (matrix {m} {n} f j i)
                     ∧ two._≤_ (matrix {m} {n} f j i) (matrix {n} {m} (transpose {m} {n} f) i j)
  transpose-matrix m n f i j rewrite proj-tabulate {m} (λ k → _⋅_ {n} (f .fun (e k)) (e j)) i = ⋅-e {n} (f .fun (e i)) j
