{-# OPTIONS --postfix-projections --prop --safe #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import prop-setoid using (module ≈-Reasoning)
open import categories using (Category; IsInitial; IsTerminal; HasInitial; HasTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)

-- Embedding of Mat(S) into a CMon-enriched category 𝒞 with binary biproducts and zero object, via a chosen
-- scalar object X whose endomorphism semiring is (isomorphic to) S. The representation functor builds the
-- SemiLat morphism for a matrix M by taking the n-ary pair of n-ary copairs of the matrix entries.
module matrix-embedding
  {o m e} {𝒞 : Category o m e}
  (CM : CMonEnriched 𝒞)
  (BP : ∀ x y → Biproduct CM x y)
  (𝟘 : Category.obj 𝒞)
  (𝟘-initial : IsInitial 𝒞 𝟘)
  (𝟘-terminal : IsTerminal 𝒞 𝟘)
  (X : Category.obj 𝒞)
  where

  open CMonEnriched CM
  open CommutativeMonoid
  open Biproduct
  open IsInitial 𝟘-initial
  open IsTerminal 𝟘-terminal
  open Category 𝒞

  _⊕_ : obj → obj → obj
  x ⊕ y = prod (BP x y)

  -- n-ary biproduct.
  X^ : ℕ → obj
  X^ zero = 𝟘
  X^ (suc n) = X ⊕ X^ n
