{-# OPTIONS --postfix-projections --prop --safe #-}

-- Matrix representation via iterated biproducts in a CMon-enriched category.
-- Parameterised over a category 𝒞 with CMon-enrichment, biproducts, a zero object, and a generator A.
-- Instantiating A to Two in SemiLat recovers the Boolean Jacobian development of bool-jacobian.agda.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import prop-setoid using (module ≈-Reasoning)
open import categories using (Category; IsInitial; IsTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)

module matrices
  {o m e} {𝒞 : Category o m e}
  (CM : CMonEnriched 𝒞)
  (BP : ∀ x y → Biproduct CM x y)
  (𝟘 : Category.obj 𝒞)
  (𝟘-initial : IsInitial 𝒞 𝟘)
  (𝟘-terminal : IsTerminal 𝒞 𝟘)
  (X : Category.obj 𝒞)
  where

  open Category 𝒞
  open CMonEnriched CM
  open CommutativeMonoid
  open Biproduct

  -- n-fold iterated biproduct of X.
  X^ : ℕ → obj
  X^ zero = 𝟘
  X^ (suc n) = prod (BP X (X^ n))

  -- i-th injection.
  ι : ∀ {n} → Fin n → X ⇒ X^ n
  ι {suc n} zero = in₁ (BP X (X^ n))
  ι {suc n} (suc i) = in₂ (BP X (X^ n)) ∘ ι i

  -- i-th projection.
  π : ∀ {n} → Fin n → X^ n ⇒ X
  π {suc n} zero = p₁ (BP X (X^ n))
  π {suc n} (suc i) = π i ∘ p₂ (BP X (X^ n))

  -- Matrix entry: the (i, j)-entry of a morphism f : X^m → X^n.
  entry : ∀ {m n} → X^ m ⇒ X^ n → Fin n → Fin m → X ⇒ X
  entry f i j = π i ∘ (f ∘ ι j)
