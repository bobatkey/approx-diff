{-# OPTIONS --postfix-projections --prop --safe #-}

-- Matrix representation via iterated biproducts in a (necessarily CMon-enriched) category with binary
-- biproducts and zero object, and base object A. Instantiating A to Two in SemiLat recovers the "Boolean
-- Jacobian" setting FDVect_2.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import prop-setoid using (module ≈-Reasoning)
open import categories using (Category; IsInitial; IsTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)

module matrices
  {o m e} {𝒞 : Category o m e}
  (CM : CMonEnriched 𝒞) -- technically derivable from BP and 𝟘, but our BP setup relies on CM
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
  open IsInitial 𝟘-initial
  open IsTerminal 𝟘-terminal

  -- n-ary biproduct.
  X^ : ℕ → obj
  X^ zero = 𝟘
  X^ (suc n) = prod (BP X (X^ n))

  private
    bp : ∀ {n} → Biproduct CM X (X^ n)
    bp {n} = BP X (X^ n)

  -- i-th injection.
  ι : ∀ {n} → Fin n → X ⇒ X^ n
  ι {suc n} zero    = in₁ bp
  ι {suc n} (suc i) = in₂ bp ∘ ι i

  -- i-th projection.
  π : ∀ {n} → Fin n → X^ n ⇒ X
  π {suc n} zero    = p₁ bp
  π {suc n} (suc i) = π i ∘ p₂ bp

  -- n-ary pair: given n morphisms Z ⇒ X, produce Z ⇒ X^n.
  pairₙ : ∀ {n Z} → (Fin n → Z ⇒ X) → Z ⇒ X^ n
  pairₙ {zero}  f = to-terminal
  pairₙ {suc n} f = pair bp (f zero) (pairₙ (f ∘ suc))

  -- n-ary copair: given n morphisms X ⇒ Z, produce X^n ⇒ Z.
  copairₙ : ∀ {n Z} → (Fin n → X ⇒ Z) → X^ n ⇒ Z
  copairₙ {zero}  f = from-initial
  copairₙ {suc n} f = copair bp (f zero) (copairₙ (f ∘ suc))

  -- Universal property of n-ary pair: π i ∘ pairₙ f ≈ f i.
  π-pairₙ : ∀ {n Z} (f : Fin n → Z ⇒ X) (i : Fin n) → (π i ∘ pairₙ f) ≈ f i
  π-pairₙ {suc n} f zero = pair-p₁ bp (f zero) (pairₙ (f ∘ suc))
  π-pairₙ {suc n} f (suc i) =
    begin
      π i ∘ (p₂ bp ∘ pairₙ f)
    ≈⟨ ≈-sym (assoc _ _ _) ⟩
      (π i ∘ p₂ bp) ∘ pairₙ f
    ≈⟨ ∘-cong ≈-refl (pair-p₂ bp (f zero) (pairₙ (f ∘ suc))) ⟩
      π i ∘ pairₙ (f ∘ suc)
    ≈⟨ π-pairₙ (f ∘ suc) i ⟩
      f (suc i)
    ∎ where open ≈-Reasoning isEquiv

  -- Universal property of n-ary copair: copairₙ f ∘ ι i ≈ f i.
  copairₙ-ι : ∀ {n Z} (f : Fin n → X ⇒ Z) (i : Fin n) → (copairₙ f ∘ ι i) ≈ f i
  copairₙ-ι {suc n} f zero = copair-in₁ bp (f zero) (copairₙ (f ∘ suc))
  copairₙ-ι {suc n} f (suc i) =
    begin
      copairₙ f ∘ (in₂ bp ∘ ι i)
    ≈⟨ assoc _ _ _ ⟩
      (copairₙ f ∘ in₂ bp) ∘ ι i
    ≈⟨ ∘-cong (copair-in₂ bp (f zero) (copairₙ (f ∘ suc))) ≈-refl ⟩
      copairₙ (f ∘ suc) ∘ ι i
    ≈⟨ copairₙ-ι (f ∘ suc) i ⟩
      f (suc i)
    ∎ where open ≈-Reasoning isEquiv

  -- Matrix entry: the (i, j)-entry of a morphism f : X^m → X^n.
  entry : ∀ {m n} → X^ m ⇒ X^ n → Fin n → Fin m → X ⇒ X
  entry f i j = π i ∘ (f ∘ ι j)
