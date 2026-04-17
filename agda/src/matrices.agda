{-# OPTIONS --postfix-projections --prop --safe #-}

-- Matrix representation via iterated biproducts in a (necessarily CMon-enriched) category with binary
-- biproducts and zero object, and base object X. Instantiating X to Two in SemiLat recovers the "Boolean
-- Jacobian" setting FDVect_2.

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
  open IsInitial 𝟘-initial
  open IsTerminal 𝟘-terminal

  -- n-ary biproduct.
  X^ : ℕ → obj
  X^ zero = 𝟘
  X^ (suc n) = prod (BP X (X^ n))

  -- 'in' would be consistent with definition in biproduct but that's a reserved word.
  ι : ∀ {n} → Fin n → X ⇒ X^ n
  ι {suc n} zero = in₁ (BP X (X^ n))
  ι {suc n} (suc i) = in₂ (BP X (X^ n)) ∘ ι i

  π : ∀ {n} → Fin n → X^ n ⇒ X
  π {suc n} zero = p₁ (BP X (X^ n))
  π {suc n} (suc i) = π i ∘ p₂ (BP X (X^ n))

  -- n-ary pair: given n morphisms Z ⇒ X, produce Z ⇒ X^n.
  pairₙ : ∀ {n Z} → (Fin n → Z ⇒ X) → Z ⇒ X^ n
  pairₙ {zero}  f = to-terminal
  pairₙ {suc n} f = pair (BP X (X^ n)) (f zero) (pairₙ (λ i → f (suc i)))

  -- n-ary copair: given n morphisms X ⇒ Z, produce X^n ⇒ Z.
  copairₙ : ∀ {n Z} → (Fin n → X ⇒ Z) → X^ n ⇒ Z
  copairₙ {zero}  f = from-initial
  copairₙ {suc n} f = copair (BP X (X^ n)) (f zero) (copairₙ (λ i → f (suc i)))

  -- Universal property of n-ary pair: π i ∘ pairₙ f ≈ f i.
  π-pairₙ : ∀ {n Z} (f : Fin n → Z ⇒ X) (i : Fin n) → (π i ∘ pairₙ f) ≈ f i
  π-pairₙ {suc n} f zero = pair-p₁ (BP X (X^ n)) (f zero) (pairₙ (λ i → f (suc i)))
  π-pairₙ {suc n} f (suc i) =
    begin
      (π i ∘ p₂ (BP X (X^ n))) ∘ pairₙ f
    ≈⟨ assoc _ _ _ ⟩
      π i ∘ (p₂ (BP X (X^ n)) ∘ pairₙ f)
    ≈⟨ ∘-cong ≈-refl (pair-p₂ (BP X (X^ n)) (f zero) (pairₙ (λ i → f (suc i)))) ⟩
      π i ∘ pairₙ (λ i → f (suc i))
    ≈⟨ π-pairₙ (λ i → f (suc i)) i ⟩
      f (suc i)
    ∎ where open ≈-Reasoning isEquiv

  -- Universal property of n-ary copair: copairₙ f ∘ ι i ≈ f i.
  copairₙ-ι : ∀ {n Z} (f : Fin n → X ⇒ Z) (i : Fin n) → (copairₙ f ∘ ι i) ≈ f i
  copairₙ-ι {suc n} f zero = copair-in₁ (BP X (X^ n)) (f zero) (copairₙ (λ i → f (suc i)))
  copairₙ-ι {suc n} f (suc i) =
    begin
      copairₙ f ∘ (in₂ (BP X (X^ n)) ∘ ι i)
    ≈˘⟨ assoc _ _ _ ⟩
      (copairₙ f ∘ in₂ (BP X (X^ n))) ∘ ι i
    ≈⟨ ∘-cong (copair-in₂ (BP X (X^ n)) (f zero) (copairₙ (λ i → f (suc i)))) ≈-refl ⟩
      copairₙ (λ i → f (suc i)) ∘ ι i
    ≈⟨ copairₙ-ι (λ i → f (suc i)) i ⟩
      f (suc i)
    ∎ where open ≈-Reasoning isEquiv

  -- Matrix entry: the (i, j)-entry of a morphism f : X^m → X^n.
  entry : ∀ {m n} → X^ m ⇒ X^ n → Fin n → Fin m → X ⇒ X
  entry f i j = π i ∘ (f ∘ ι j)
