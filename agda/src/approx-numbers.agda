{-# OPTIONS --postfix-projections --prop --safe #-}

module approx-numbers where

open import Level using (0ℓ; suc)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import prop using (⊤; tt; ⊥; LiftS; liftS; _∧_; _,_; proj₁; proj₂)
open import prop-setoid using (Setoid; IsEquivalence)
open import preorder using (Preorder; _=>_; bottom; <_>)
open import meet-semilattice using (MeetSemilattice)
open import join-semilattice using (JoinSemilattice)
  renaming (_=>_ to _=>J_; module _=>_ to _=>J_)
open import basics using (IsPreorder; IsMeet; IsTop; IsJoin; IsBottom)

open import categories using (HasTerminal; Category)
open import galois using (Obj; _⊕_; _⇒g_)

import fam

open import Data.Rational using (ℚ; _≤_; _⊔_; _⊓_; _+_; _-_; 0ℚ; -_; Positive; _*_; _÷_; NonZero)
open import Data.Rational.Properties
  using (
    ≤-refl; ≤-trans; ⊓-glb; ⊔-lub; p⊓q≤p; p⊓q≤q; +-mono-≤; module ≤-Reasoning; +-comm; ≤-reflexive; +-assoc;
    +-inverseʳ; +-inverseˡ; +-identityʳ; +-identityˡ; ⊓-mono-≤; p≤p⊔q; p≤q⊔p; neg-antimono-≤; pos⇒nonZero; pos⇒nonNeg;
    *-monoˡ-≤-nonNeg; ⊔-mono-≤; ⊓-distribˡ-⊔; ⊔-distribˡ-⊓; mono-≤-distrib-⊔; mono-≤-distrib-⊓; ⊔-comm; ⊓-comm;
    ⊔-assoc; ⊓-assoc
  )
open import Relation.Binary.PropositionalEquality using (cong; _≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

open IsPreorder

------------------------------------------------------------------------------
module Fam⟨LatGal⟩ = fam.CategoryOfFamilies 0ℓ 0ℓ galois.cat

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat = Fam⟨LatGal⟩.cat

module C = Category cat

open Fam⟨LatGal⟩.products galois.products
  using (products; simple-monoidal; _⊗_)

terminal : HasTerminal cat
terminal = Fam⟨LatGal⟩.terminal galois.terminal

𝟙 = terminal .HasTerminal.witness

------------------------------------------------------------------------------
adjoint₁ : ∀ {x y z} → x ≤ y + z → x - y ≤ z
adjoint₁ {x} {y} {z} ϕ = begin
    x - y
  ≤⟨ +-mono-≤ ϕ ≤-refl ⟩
    (y + z) - y
  ≤⟨ +-mono-≤ (≤-reflexive (+-comm y z)) ≤-refl ⟩
    (z + y) - y
  ≤⟨ ≤-reflexive (+-assoc z y (- y)) ⟩
    z + (y - y)
  ≤⟨ +-mono-≤ (≤-refl {z}) (≤-reflexive (+-inverseʳ y)) ⟩
    z + 0ℚ
  ≤⟨ ≤-reflexive (+-identityʳ z) ⟩
    z
  ∎
  where open ≤-Reasoning

adjoint₂ : ∀ {x y z} → x - y ≤ z → x ≤ y + z
adjoint₂ {x} {y} {z} ϕ = begin
    x
  ≤⟨ ≤-reflexive (≡-sym (+-identityˡ x)) ⟩
    0ℚ + x
  ≤⟨ +-mono-≤ (≤-reflexive (≡-sym (+-inverseʳ y))) ≤-refl ⟩
    (y + (- y)) + x
  ≤⟨ ≤-reflexive (+-assoc y (- y) x) ⟩
    y + ((- y) + x)
  ≤⟨ +-mono-≤ (≤-refl {y}) (≤-reflexive (+-comm (- y) x)) ⟩
    y + (x - y)
  ≤⟨ +-mono-≤ (≤-refl {y}) ϕ ⟩
    y + z
  ∎
  where open ≤-Reasoning

adjoint₂' : ∀ {x y z} → x + y ≤ z → y ≤ z - x
adjoint₂' {x} {y} {z} ϕ = begin
    y
  ≡˘⟨ +-identityʳ y ⟩
    y + 0ℚ
  ≡˘⟨ cong (λ □ → y + □) (+-inverseʳ x) ⟩
    y + (x - x)
  ≡˘⟨ +-assoc y x (- x) ⟩
    (y + x) - x
  ≡⟨ cong (λ □ → □ - x) (+-comm y x) ⟩
    (x + y) - x
  ≤⟨ +-mono-≤ ϕ (≤-refl { - x}) ⟩
    z - x
  ∎
  where open ≤-Reasoning

adjoint₁' : ∀ {x y z} → x ≤ y - z → z + x ≤ y
adjoint₁' {x} {y} {z} ϕ = begin
    z + x
  ≤⟨ +-mono-≤ (≤-refl {z}) ϕ ⟩
    z + (y - z)
  ≡⟨ cong (λ □ → z + □) (+-comm y (- z)) ⟩
    z + ((- z) + y)
  ≡˘⟨ +-assoc z (- z) y ⟩
    (z + (- z)) + y
  ≡⟨ cong (λ □ → □ + y) (+-inverseʳ z) ⟩
    0ℚ + y
  ≡⟨ +-identityˡ y ⟩
    y
  ∎
  where open ≤-Reasoning

------------------------------------------------------------------------------
-- Intervals, without bottom

record Intv (q : ℚ) : Set where
  field
    lower : ℚ
    upper : ℚ
    l≤q   : LiftS 0ℓ (lower ≤ q)
    q≤u   : LiftS 0ℓ (q ≤ upper)
open Intv

_⊑_ : ∀ {q} → Intv q → Intv q → Prop
x ⊑ y = LiftS 0ℓ (x .lower ≤ y .lower) ∧ LiftS 0ℓ (y .upper ≤ x .upper)

⊑I-isPreorder : ∀ {q} → IsPreorder (_⊑_ {q})
⊑I-isPreorder .refl = (liftS ≤-refl) , (liftS ≤-refl)
⊑I-isPreorder .trans (liftS ϕ₁ , liftS ϕ₂) (liftS ψ₁ , liftS ψ₂) =
  (liftS (≤-trans ϕ₁ ψ₁)) , (liftS (≤-trans ψ₂ ϕ₂))

IntvPreorder : ℚ → Preorder
IntvPreorder q .Preorder.Carrier = Intv q
IntvPreorder q .Preorder._≤_ = _⊑_
IntvPreorder q .Preorder.≤-isPreorder = ⊑I-isPreorder

_⊓I_ : ∀ {q} → Intv q → Intv q → Intv q
(x ⊓I y) .lower = x .lower ⊓ y .lower
(x ⊓I y) .upper = x .upper ⊔ y .upper
(x ⊓I y) .l≤q with x .l≤q
... | liftS ϕ = liftS (≤-trans (p⊓q≤p _ _) ϕ)
(x ⊓I y) .q≤u with x .q≤u
... | liftS ϕ = liftS (≤-trans ϕ (p≤p⊔q _ _))

⊤I : ∀ {q} → Intv q
⊤I {q} .lower = q
⊤I {q} .upper = q
⊤I {q} .l≤q = liftS ≤-refl
⊤I {q} .q≤u = liftS ≤-refl

⊤I-isTop : ∀ {q} → IsTop (⊑I-isPreorder {q}) ⊤I
⊤I-isTop .IsTop.≤-top {x} = x .l≤q , x .q≤u

⊓I-isMeet : ∀ {q} → IsMeet (⊑I-isPreorder {q}) _⊓I_
⊓I-isMeet .IsMeet.π₁ = liftS (p⊓q≤p _ _) , liftS (p≤p⊔q _ _)
⊓I-isMeet .IsMeet.π₂ {x} {y} = liftS (p⊓q≤q (x .lower) _) , liftS (p≤q⊔p (x .upper) _)
⊓I-isMeet .IsMeet.⟨_,_⟩ (liftS ϕ₁ , liftS ϕ₂) (liftS ψ₁ , liftS ψ₂) =
  liftS (⊓-glb ϕ₁ ψ₁) , liftS (⊔-lub ϕ₂ ψ₂)

meets : ∀ q → MeetSemilattice (IntvPreorder q)
meets q .MeetSemilattice._∧_ = _⊓I_
meets q .MeetSemilattice.⊤ = ⊤I
meets q .MeetSemilattice.∧-isMeet = ⊓I-isMeet
meets q .MeetSemilattice.⊤-isTop = ⊤I-isTop

_⊔I_ : ∀ {q} → Intv q → Intv q → Intv q
(x ⊔I y) .lower = x .lower ⊔ y .lower
(x ⊔I y) .upper = x .upper ⊓ y .upper
(x ⊔I y) .l≤q with x .l≤q
... | liftS ϕ with y .l≤q
... | liftS ψ = liftS (⊔-lub ϕ ψ)
(x ⊔I y) .q≤u with (x .q≤u)
... | liftS ϕ with (y .q≤u)
... | liftS ψ = liftS (⊓-glb ϕ ψ)

⊔I-isJoin : ∀ {q} → IsJoin (⊑I-isPreorder {q}) _⊔I_
⊔I-isJoin .IsJoin.inl = liftS (p≤p⊔q _ _) , liftS (p⊓q≤p _ _)
⊔I-isJoin .IsJoin.inr {x} = liftS (p≤q⊔p (x .lower) _) , liftS (p⊓q≤q (x .upper) _)
⊔I-isJoin .IsJoin.[_,_] (liftS ϕ₁ , liftS ϕ₂) (liftS ψ₁ , liftS ψ₂) =
  liftS (⊔-lub ϕ₁ ψ₁) , liftS (⊓-glb ϕ₂ ψ₂)

------------------------------------------------------------------------------
-- Addition

-- Join-preserving backwards map.
add : ∀ q₁ q₂ → Intv (q₁ + q₂) → Intv q₁ × Intv q₂
add q₁ q₂ x .proj₁ .lower = x .lower - q₂
add q₁ q₂ x .proj₁ .upper = x .upper - q₂
add q₁ q₂ x .proj₁ .l≤q with (x .l≤q)
... | liftS ϕ = liftS (adjoint₁ {x .lower} {q₂} {q₁} (≤-trans ϕ (≤-reflexive (+-comm q₁ q₂))))
add q₁ q₂ x .proj₁ .q≤u with (x .q≤u)
... | liftS ϕ = liftS (adjoint₂' {q₂} {q₁} {x .upper} (≤-trans (≤-reflexive (+-comm q₂ q₁)) ϕ))
add q₁ q₂ x .proj₂ .lower = x .lower - q₁
add q₁ q₂ x .proj₂ .upper = x .upper - q₁
add q₁ q₂ x .proj₂ .l≤q with x .l≤q
... | liftS ϕ = liftS (adjoint₁ {x .lower} {q₁} {q₂} ϕ)
add q₁ q₂ x .proj₂ .q≤u with x .q≤u
... | liftS ϕ = liftS (adjoint₂' {q₁} {q₂} {x .upper} ϕ)

-- Meet-preserving forwards map (right adjoint).
add⁎ : ∀ q₁ q₂ → Intv q₁ → Intv q₂ → Intv (q₁ + q₂)
add⁎ q₁ q₂ x y .lower = (q₂ + x .lower) ⊓ (q₁ + y .lower)
add⁎ q₁ q₂ x y .upper = (q₂ + x .upper) ⊔ (q₁ + y .upper)
add⁎ q₁ q₂ x y .l≤q with y .l≤q
... | liftS ϕ = liftS (≤-trans (p⊓q≤q (q₂ + x .lower) (q₁ + y .lower)) (+-mono-≤ (≤-refl {q₁}) ϕ))
add⁎ q₁ q₂ x y .q≤u with (y .q≤u)
... | liftS ϕ = liftS (≤-trans (+-mono-≤ (≤-refl {q₁}) ϕ) (p≤q⊔p (q₂ + x .upper) _))

-- Join-preserving forwards map (conjugate).
addᵀ : ∀ q₁ q₂ → Intv q₁ → Intv q₂ → Intv (q₁ + q₂)
addᵀ q₁ q₂ x y .lower = (q₂ + x .lower) ⊔ (q₁ + y .lower)
addᵀ q₁ q₂ x y .upper = (q₂ + x .upper) ⊓ (q₁ + y .upper)
addᵀ q₁ q₂ x y .l≤q with x .l≤q | y .l≤q
... | liftS ϕ | liftS ψ =
  liftS (⊔-lub (≤-trans (+-mono-≤ (≤-refl {q₂}) ϕ) (≤-reflexive (+-comm q₂ q₁)))
               (+-mono-≤ (≤-refl {q₁}) ψ))
addᵀ q₁ q₂ x y .q≤u with x .q≤u | y .q≤u
... | liftS ϕ | liftS ψ =
  liftS (⊓-glb (≤-trans (≤-reflexive (+-comm q₁ q₂)) (+-mono-≤ (≤-refl {q₂}) ϕ))
               (+-mono-≤ (≤-refl {q₁}) ψ))

galois₁ : ∀ q₁ q₂ x y z →
          z ⊑ (add⁎ q₁ q₂ x y) → (add q₁ q₂ z .proj₁ ⊑ x) ∧ (add q₁ q₂ z .proj₂ ⊑ y)
galois₁ q₁ q₂ x y z (liftS ϕ₁ , liftS ϕ₂) .proj₁ =
  liftS (adjoint₁ {z .lower} {q₂} {x .lower} (≤-trans ϕ₁ (p⊓q≤p _ _))) ,
  liftS (adjoint₂' {q₂} {x .upper} {z .upper} (≤-trans (p≤p⊔q (q₂ + x .upper) (q₁ + y .upper)) ϕ₂))
galois₁ q₁ q₂ x y z (liftS ϕ₁ , liftS ϕ₂) .proj₂ =
  liftS (adjoint₁ {z .lower} {q₁} {y .lower} (≤-trans ϕ₁ (p⊓q≤q (q₂ + x .lower) _))) ,
  liftS (adjoint₂' {q₁} {y .upper} {z .upper} (≤-trans (p≤q⊔p (q₂ + x .upper) (q₁ + y .upper)) ϕ₂))

galois₂ : ∀ q₁ q₂ x y z →
          (add q₁ q₂ z .proj₁ ⊑ x) ∧ (add q₁ q₂ z .proj₂ ⊑ y) → z ⊑ (add⁎ q₁ q₂ x y)
galois₂ q₁ q₂ x y z ((liftS ϕ₁ , liftS ϕ₂) , (liftS ψ₁ , liftS ψ₂)) =
  liftS (⊓-glb (adjoint₂ ϕ₁) (adjoint₂ ψ₁)) ,
  liftS (⊔-lub (adjoint₁' ϕ₂) (adjoint₁' ψ₂))

add⁎-mono : ∀ q₁ q₂ {x₁ x₂ y₁ y₂} → x₁ ⊑ x₂ → y₁ ⊑ y₂ → add⁎ q₁ q₂ x₁ y₁ ⊑ add⁎ q₁ q₂ x₂ y₂
add⁎-mono q₁ q₂ (liftS ϕ₁ , liftS ϕ₂) (liftS ψ₁ , liftS ψ₂) =
  liftS (⊓-mono-≤ (+-mono-≤ (≤-refl {q₂}) ϕ₁) (+-mono-≤ (≤-refl {q₁}) ψ₁)) ,
  liftS (⊔-mono-≤ (+-mono-≤ (≤-refl {q₂}) ϕ₂) (+-mono-≤ (≤-refl {q₁}) ψ₂))

addᵀ-mono : ∀ q₁ q₂ {x₁ x₂ y₁ y₂} → x₁ ⊑ x₂ → y₁ ⊑ y₂ → addᵀ q₁ q₂ x₁ y₁ ⊑ addᵀ q₁ q₂ x₂ y₂
addᵀ-mono q₁ q₂ (liftS ϕ₁ , liftS ϕ₂) (liftS ψ₁ , liftS ψ₂) =
  liftS (⊔-mono-≤ (+-mono-≤ (≤-refl {q₂}) ϕ₁) (+-mono-≤ (≤-refl {q₁}) ψ₁)) ,
  liftS (⊓-mono-≤ (+-mono-≤ (≤-refl {q₂}) ϕ₂) (+-mono-≤ (≤-refl {q₁}) ψ₂))

addᵀ-r : ∀ q₁ q₂ → Intv q₁ → Intv (q₁ + q₂)
addᵀ-r q₁ q₂ x .lower = q₂ + x .lower
addᵀ-r q₁ q₂ x .upper = q₂ + x .upper
addᵀ-r q₁ q₂ x .l≤q with x .l≤q
... | liftS ϕ = liftS (≤-trans (+-mono-≤ (≤-refl {q₂}) ϕ) (≤-reflexive (+-comm q₂ q₁)))
addᵀ-r q₁ q₂ x .q≤u with x .q≤u
... | liftS ϕ = liftS (≤-trans (≤-reflexive (+-comm q₁ q₂)) (+-mono-≤ (≤-refl {q₂}) ϕ))

addᵀ-l : ∀ q₁ q₂ → Intv q₂ → Intv (q₁ + q₂)
addᵀ-l q₁ q₂ y .lower = q₁ + y .lower
addᵀ-l q₁ q₂ y .upper = q₁ + y .upper
addᵀ-l q₁ q₂ y .l≤q with y .l≤q
... | liftS ϕ = liftS (+-mono-≤ (≤-refl {q₁}) ϕ)
addᵀ-l q₁ q₂ y .q≤u with y .q≤u
... | liftS ϕ = liftS (+-mono-≤ (≤-refl {q₁}) ϕ)

addᵀ-r-mono : ∀ q₁ q₂ {x₁ x₂} → x₁ ⊑ x₂ → addᵀ-r q₁ q₂ x₁ ⊑ addᵀ-r q₁ q₂ x₂
addᵀ-r-mono q₁ q₂ (liftS ϕ₁ , liftS ϕ₂) =
  liftS (+-mono-≤ (≤-refl {q₂}) ϕ₁) , liftS (+-mono-≤ (≤-refl {q₂}) ϕ₂)

addᵀ-l-mono : ∀ q₁ q₂ {y₁ y₂} → y₁ ⊑ y₂ → addᵀ-l q₁ q₂ y₁ ⊑ addᵀ-l q₁ q₂ y₂
addᵀ-l-mono q₁ q₂ (liftS ϕ₁ , liftS ϕ₂) =
  liftS (+-mono-≤ (≤-refl {q₁}) ϕ₁) , liftS (+-mono-≤ (≤-refl {q₁}) ϕ₂)

-- addᵀ as the join of the two partial-input contributions; basis of join-preservation.
addᵀ-split-≤ : ∀ q₁ q₂ x y → addᵀ q₁ q₂ x y ⊑ (addᵀ-r q₁ q₂ x ⊔I addᵀ-l q₁ q₂ y)
addᵀ-split-≤ q₁ q₂ x y = ⊑I-isPreorder .refl {addᵀ q₁ q₂ x y}

addᵀ-split-≥ : ∀ q₁ q₂ x y → (addᵀ-r q₁ q₂ x ⊔I addᵀ-l q₁ q₂ y) ⊑ addᵀ q₁ q₂ x y
addᵀ-split-≥ q₁ q₂ x y = ⊑I-isPreorder .refl {addᵀ q₁ q₂ x y}

------------------------------------------------------------------------------
IntervalG : ℚ → Obj
IntervalG q .galois.Obj.carrier = preorder.L (IntvPreorder q)
IntervalG q .galois.Obj.meets = meet-semilattice.L (meets q)
IntervalG q .galois.Obj.joins = join-semilattice.L₀ ⊔I-isJoin

add-intervalG : ∀ q₁ q₂ → (IntervalG q₁ ⊕ IntervalG q₂) ⇒g IntervalG (q₁ + q₂)
add-intervalG q₁ q₂ ._⇒g_.right ._=>_.fun (bottom , bottom) = bottom
add-intervalG q₁ q₂ ._⇒g_.right ._=>_.fun (bottom , < x >) = bottom
add-intervalG q₁ q₂ ._⇒g_.right ._=>_.fun (< x > , bottom) = bottom
add-intervalG q₁ q₂ ._⇒g_.right ._=>_.fun (< x > , < y >) = < add⁎ q₁ q₂ x y >
add-intervalG q₁ q₂ ._⇒g_.right ._=>_.mono {bottom , bottom} {x₂ , y₂} ϕ = tt
add-intervalG q₁ q₂ ._⇒g_.right ._=>_.mono {bottom , < x >} {x₂ , y₂} ϕ = tt
add-intervalG q₁ q₂ ._⇒g_.right ._=>_.mono {< x > , bottom} {x₂ , y₂} ϕ = tt
add-intervalG q₁ q₂ ._⇒g_.right ._=>_.mono {< x₁ > , < y₁ >} {< x₂ > , < y₂ >} (x₁≤x₂ , y₁≤y₂) =
  add⁎-mono q₁ q₂ {x₁} {x₂} {y₁} {y₂} x₁≤x₂ y₁≤y₂
add-intervalG q₁ q₂ ._⇒g_.left ._=>_.fun bottom = bottom , bottom
add-intervalG q₁ q₂ ._⇒g_.left ._=>_.fun < x > = < add q₁ q₂ x .proj₁ > , < add q₁ q₂ x .proj₂ >
add-intervalG q₁ q₂ ._⇒g_.left ._=>_.mono {bottom} {y} ϕ = tt , tt
add-intervalG q₁ q₂ ._⇒g_.left ._=>_.mono {< x >} {< y >} (liftS ϕ₁ , liftS ϕ₂) .proj₁ =
  liftS (+-mono-≤ ϕ₁ ≤-refl) , liftS (+-mono-≤ ϕ₂ ≤-refl)
add-intervalG q₁ q₂ ._⇒g_.left ._=>_.mono {< x >} {< y >} (liftS ϕ₁ , liftS ϕ₂) .proj₂ =
  liftS (+-mono-≤ ϕ₁ ≤-refl) , liftS (+-mono-≤ ϕ₂ ≤-refl)
add-intervalG q₁ q₂ ._⇒g_.left⊣right {bottom , bottom} {bottom} = (λ _ → tt , tt) , (λ _ → tt)
add-intervalG q₁ q₂ ._⇒g_.left⊣right {bottom , bottom} {< x >} = (λ ()) , λ ()
add-intervalG q₁ q₂ ._⇒g_.left⊣right {bottom , < y >} {bottom} = (λ _ → tt , tt) , (λ _ → tt)
add-intervalG q₁ q₂ ._⇒g_.left⊣right {bottom , < y >} {< z >} = (λ ()) , (λ ())
add-intervalG q₁ q₂ ._⇒g_.left⊣right {< x > , bottom} {bottom} = (λ _ → tt , tt) , (λ _ → tt)
add-intervalG q₁ q₂ ._⇒g_.left⊣right {< x > , bottom} {< z >} = (λ ()) , (λ ())
add-intervalG q₁ q₂ ._⇒g_.left⊣right {< x > , < y >} {bottom} = (λ _ → tt , tt) , (λ _ → tt)
add-intervalG q₁ q₂ ._⇒g_.left⊣right {< x > , < y >} {< z >} .proj₁ = galois₁ q₁ q₂ x y z
add-intervalG q₁ q₂ ._⇒g_.left⊣right {< x > , < y >} {< z >} .proj₂ = galois₂ q₁ q₂ x y z

open import conjugate
  using (_⇒c_; module _⇒c_)
  renaming (Obj to ObjC; module Obj to ObjC; _⊕_ to _⊕c_)

IntervalC : ℚ → ObjC
IntervalC q .ObjC.carrier = preorder.L (IntvPreorder q)
IntervalC q .ObjC.meets = meet-semilattice.L (meets q)
IntervalC q .ObjC.joins = join-semilattice.L₀ ⊔I-isJoin
IntervalC q .ObjC.∧-∨-distrib bottom _ _ = tt
IntervalC q .ObjC.∧-∨-distrib < _ > bottom bottom = tt
IntervalC q .ObjC.∧-∨-distrib < x > bottom < z > = ⊑I-isPreorder .refl {x ⊓I z}
IntervalC q .ObjC.∧-∨-distrib < x > < y > bottom = ⊑I-isPreorder .refl {x ⊓I y}
IntervalC q .ObjC.∧-∨-distrib < x > < y >  < z > .proj₁ =
  liftS (≤-reflexive (⊓-distribˡ-⊔ (x .lower) (y .lower) (z .lower)))
IntervalC q .ObjC.∧-∨-distrib < x > < y >  < z > .proj₂ =
  liftS (≤-reflexive (≡-sym (⊔-distribˡ-⊓ (x .upper) (y .upper) (z .upper))))

add-intervalC : ∀ q₁ q₂ → (IntervalC q₁ ⊕c IntervalC q₂) ⇒c IntervalC (q₁ + q₂)
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.func ._=>_.fun (bottom , bottom) = bottom
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.func ._=>_.fun (< x > , bottom) = < addᵀ-r q₁ q₂ x >
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.func ._=>_.fun (bottom , < y >) = < addᵀ-l q₁ q₂ y >
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.func ._=>_.fun (< x > , < y >) = < addᵀ q₁ q₂ x y >
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.func ._=>_.mono {bottom , bottom} _ = tt
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.func ._=>_.mono {< a > , bottom} {< a' > , bottom} (ϕ , _) =
  addᵀ-r-mono q₁ q₂ {a} {a'} ϕ
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.func ._=>_.mono {< a > , bottom} {< a' > , < b' >} ((liftS ϕ₁ , liftS ϕ₂) , _) =
  liftS (≤-trans (+-mono-≤ (≤-refl {q₂}) ϕ₁) (p≤p⊔q (q₂ + a' .lower) (q₁ + b' .lower))) ,
  liftS (≤-trans (p⊓q≤p (q₂ + a' .upper) (q₁ + b' .upper)) (+-mono-≤ (≤-refl {q₂}) ϕ₂))
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.func ._=>_.mono {bottom , < b >} {bottom , < b' >} (_ , ψ) =
  addᵀ-l-mono q₁ q₂ {b} {b'} ψ
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.func ._=>_.mono {bottom , < b >} {< a' > , < b' >} (_ , liftS ψ₁ , liftS ψ₂) =
  liftS (≤-trans (+-mono-≤ (≤-refl {q₁}) ψ₁) (p≤q⊔p (q₂ + a' .lower) (q₁ + b' .lower))) ,
  liftS (≤-trans (p⊓q≤q (q₂ + a' .upper) (q₁ + b' .upper)) (+-mono-≤ (≤-refl {q₁}) ψ₂))
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.func ._=>_.mono {< a > , < b >} {< a' > , < b' >} (ϕ , ψ) =
  addᵀ-mono q₁ q₂ {a} {a'} {b} {b'} ϕ ψ
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {bottom , bottom} {bottom , bottom} = tt
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {bottom , bottom} {< c > , bottom} =
  ⊑I-isPreorder .refl {addᵀ-r q₁ q₂ c}
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {bottom , bottom} {bottom , < d >} =
  ⊑I-isPreorder .refl {addᵀ-l q₁ q₂ d}
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {bottom , bottom} {< c > , < d >} =
  ⊑I-isPreorder .refl {addᵀ q₁ q₂ c d}
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {< a > , bottom} {bottom , bottom} =
  ⊑I-isPreorder .refl {addᵀ-r q₁ q₂ a}
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {< a > , bottom} {< c > , bottom} =
  liftS (≤-reflexive (mono-≤-distrib-⊔ (+-mono-≤ (≤-refl {q₂})) (a .lower) (c .lower))) ,
  liftS (≤-reflexive (≡-sym (mono-≤-distrib-⊓ (+-mono-≤ (≤-refl {q₂})) (a .upper) (c .upper))))
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {< a > , bottom} {bottom , < d >} =
  ⊑I-isPreorder .refl {addᵀ q₁ q₂ a d}
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {< a > , bottom} {< c > , < d >} =
  liftS (≤-reflexive (≡-trans (cong (_⊔ (q₁ + d .lower))
                                    (mono-≤-distrib-⊔ (+-mono-≤ (≤-refl {q₂})) (a .lower) (c .lower)))
                              (⊔-assoc (q₂ + a .lower) (q₂ + c .lower) (q₁ + d .lower)))) ,
  liftS (≤-reflexive (≡-trans (≡-sym (⊓-assoc (q₂ + a .upper) (q₂ + c .upper) (q₁ + d .upper)))
                              (cong (_⊓ (q₁ + d .upper))
                                    (≡-sym (mono-≤-distrib-⊓ (+-mono-≤ (≤-refl {q₂})) (a .upper) (c .upper))))))
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {bottom , < b >} {bottom , bottom} =
  ⊑I-isPreorder .refl {addᵀ-l q₁ q₂ b}
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {bottom , < b >} {< c > , bottom} =
  liftS (≤-reflexive (⊔-comm (q₂ + c .lower) (q₁ + b .lower))) ,
  liftS (≤-reflexive (⊓-comm (q₁ + b .upper) (q₂ + c .upper)))
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {bottom , < b >} {bottom , < d >} =
  liftS (≤-reflexive (mono-≤-distrib-⊔ (+-mono-≤ (≤-refl {q₁})) (b .lower) (d .lower))) ,
  liftS (≤-reflexive (≡-sym (mono-≤-distrib-⊓ (+-mono-≤ (≤-refl {q₁})) (b .upper) (d .upper))))
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {bottom , < b >} {< c > , < d >} = {!!}
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {< a > , < b >} {bottom , bottom} =
  ⊑I-isPreorder .refl {addᵀ q₁ q₂ a b}
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {< a > , < b >} {< c > , bottom} = {!!}
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {< a > , < b >} {bottom , < d >} = {!!}
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.∨-preserving {< a > , < b >} {< c > , < d >} = {!!}
add-intervalC q₁ q₂ ._⇒c_.right ._=>J_.⊥-preserving = tt
add-intervalC q₁ q₂ ._⇒c_.left ._=>J_.func ._=>_.fun bottom = bottom , bottom
add-intervalC q₁ q₂ ._⇒c_.left ._=>J_.func ._=>_.fun < z > = < add q₁ q₂ z .proj₁ > , < add q₁ q₂ z .proj₂ >
add-intervalC q₁ q₂ ._⇒c_.left ._=>J_.func ._=>_.mono {bottom} {_} _ = tt , tt
add-intervalC q₁ q₂ ._⇒c_.left ._=>J_.func ._=>_.mono {< x >} {< y >} (liftS ϕ₁ , liftS ϕ₂) .proj₁ =
  liftS (+-mono-≤ ϕ₁ ≤-refl) , liftS (+-mono-≤ ϕ₂ ≤-refl)
add-intervalC q₁ q₂ ._⇒c_.left ._=>J_.func ._=>_.mono {< x >} {< y >} (liftS ϕ₁ , liftS ϕ₂) .proj₂ =
  liftS (+-mono-≤ ϕ₁ ≤-refl) , liftS (+-mono-≤ ϕ₂ ≤-refl)
add-intervalC q₁ q₂ ._⇒c_.left ._=>J_.∨-preserving {bottom} {bottom} = tt , tt
add-intervalC q₁ q₂ ._⇒c_.left ._=>J_.∨-preserving {bottom} {< x >} = {!!} , {!!}
add-intervalC q₁ q₂ ._⇒c_.left ._=>J_.∨-preserving {< x >} {bottom} = {!!} , {!!}
add-intervalC q₁ q₂ ._⇒c_.left ._=>J_.∨-preserving {< x >} {< y >} = {!!} , {!!}
add-intervalC q₁ q₂ ._⇒c_.left ._=>J_.⊥-preserving = tt , tt
add-intervalC q₁ q₂ ._⇒c_.conjugate {bottom , bottom} {bottom} .proj₁ _ = tt , tt
add-intervalC q₁ q₂ ._⇒c_.conjugate {bottom , bottom} {bottom} .proj₂ _ = tt
add-intervalC q₁ q₂ ._⇒c_.conjugate {bottom , bottom} {< _ >} .proj₁ _ = tt , tt
add-intervalC q₁ q₂ ._⇒c_.conjugate {bottom , bottom} {< _ >} .proj₂ _ = tt
add-intervalC q₁ q₂ ._⇒c_.conjugate {bottom , < _ >} {bottom} .proj₁ _ = tt , tt
add-intervalC q₁ q₂ ._⇒c_.conjugate {bottom , < _ >} {bottom} .proj₂ _ = tt
add-intervalC q₁ q₂ ._⇒c_.conjugate {bottom , < _ >} {< _ >} .proj₁ ()
add-intervalC q₁ q₂ ._⇒c_.conjugate {bottom , < _ >} {< _ >} .proj₂ (_ , ())
add-intervalC q₁ q₂ ._⇒c_.conjugate {< _ > , bottom} {bottom} .proj₁ _ = tt , tt
add-intervalC q₁ q₂ ._⇒c_.conjugate {< _ > , bottom} {bottom} .proj₂ _ = tt
add-intervalC q₁ q₂ ._⇒c_.conjugate {< _ > , bottom} {< _ >} .proj₁ ()
add-intervalC q₁ q₂ ._⇒c_.conjugate {< _ > , bottom} {< _ >} .proj₂ (() , _)
add-intervalC q₁ q₂ ._⇒c_.conjugate {< _ > , < _ >} {bottom} .proj₁ _ = tt , tt
add-intervalC q₁ q₂ ._⇒c_.conjugate {< _ > , < _ >} {bottom} .proj₂ _ = tt
add-intervalC q₁ q₂ ._⇒c_.conjugate {< _ > , < _ >} {< _ >} .proj₁ ()
add-intervalC q₁ q₂ ._⇒c_.conjugate {< _ > , < _ >} {< _ >} .proj₂ (() , _)

------------------------------------------------------------------------------
--

import indexed-family

open Fam⟨LatGal⟩.Obj
open Fam⟨LatGal⟩.Mor
open indexed-family.Fam
open indexed-family._⇒f_


open Setoid

ℚ-setoid : Setoid 0ℓ 0ℓ
ℚ-setoid .Setoid.Carrier = ℚ
ℚ-setoid .Setoid._≈_ q₁ q₂ = LiftS 0ℓ (q₁ ≡ q₂)
ℚ-setoid .Setoid.isEquivalence .IsEquivalence.refl = liftS ≡-refl
ℚ-setoid .Setoid.isEquivalence .IsEquivalence.sym (liftS eq) = liftS (≡-sym eq)
ℚ-setoid .Setoid.isEquivalence .IsEquivalence.trans (liftS eq₁) (liftS eq₂) = liftS (≡-trans eq₁ eq₂)

subst-Intv : ∀ q₁ q₂ → LiftS 0ℓ (q₁ ≡ q₂) → Intv q₁ → Intv q₂
subst-Intv q₁ q₂ eq x .lower = x .lower
subst-Intv q₁ q₂ eq x .upper = x .upper
subst-Intv q₁ q₂ (liftS ≡-refl) x .l≤q = x .l≤q
subst-Intv q₁ q₂ (liftS ≡-refl) x .q≤u = x .q≤u

subst-Interval : ∀ q₁ q₂ → LiftS 0ℓ (q₁ ≡ q₂) → IntervalG q₁ ⇒g IntervalG q₂
subst-Interval q₁ q₂ eq ._⇒g_.right ._=>_.fun bottom = bottom
subst-Interval q₁ q₂ eq ._⇒g_.right ._=>_.fun < x > = < subst-Intv q₁ q₂ eq x >
subst-Interval q₁ q₂ eq ._⇒g_.right ._=>_.mono {bottom} {x₂} _ = tt
subst-Interval q₁ q₂ eq ._⇒g_.right ._=>_.mono {< x >} {< y >} ϕ = ϕ
subst-Interval q₁ q₂ eq ._⇒g_.left ._=>_.fun bottom = bottom
subst-Interval q₁ q₂ eq ._⇒g_.left ._=>_.fun < x > = < subst-Intv q₂ q₁ (ℚ-setoid .sym eq) x >
subst-Interval q₁ q₂ eq ._⇒g_.left ._=>_.mono {bottom} {_} ϕ = tt
subst-Interval q₁ q₂ eq ._⇒g_.left ._=>_.mono {< x >} {< y >} ϕ = ϕ
subst-Interval q₁ q₂ eq ._⇒g_.left⊣right {bottom} {bottom} .proj₁ ϕ = tt
subst-Interval q₁ q₂ eq ._⇒g_.left⊣right {< x >} {bottom} .proj₁ ϕ = tt
subst-Interval q₁ q₂ eq ._⇒g_.left⊣right {< x >} {< x₁ >} .proj₁ ϕ = ϕ
subst-Interval q₁ q₂ eq ._⇒g_.left⊣right {bottom} {bottom} .proj₂ ϕ = tt
subst-Interval q₁ q₂ eq ._⇒g_.left⊣right {< x >} {bottom} .proj₂ ϕ = tt
subst-Interval q₁ q₂ eq ._⇒g_.left⊣right {< x >} {< y >} .proj₂ ϕ = ϕ

open galois._≃g_
open preorder._≃m_

ℚ-intv : C.obj
ℚ-intv .idx = ℚ-setoid
ℚ-intv .fam .fm = IntervalG
ℚ-intv .fam .subst eq = subst-Interval _ _ eq
ℚ-intv .fam .refl* .right-eq .eqfun bottom = tt , tt
ℚ-intv .fam .refl* .right-eq .eqfun < x > = (liftS ≤-refl , liftS ≤-refl) , liftS ≤-refl , liftS ≤-refl
ℚ-intv .fam .refl* .left-eq .eqfun bottom = tt , tt
ℚ-intv .fam .refl* .left-eq .eqfun < x > = (liftS ≤-refl , liftS ≤-refl) , liftS ≤-refl , liftS ≤-refl
ℚ-intv .fam .trans* (liftS ≡-refl) (liftS ≡-refl) .right-eq .eqfun bottom = tt , tt
ℚ-intv .fam .trans* (liftS ≡-refl) (liftS ≡-refl) .right-eq .eqfun < x > = (liftS ≤-refl , liftS ≤-refl) , liftS ≤-refl , liftS ≤-refl
ℚ-intv .fam .trans* (liftS ≡-refl) (liftS ≡-refl) .left-eq .eqfun bottom = tt , tt
ℚ-intv .fam .trans* (liftS ≡-refl) (liftS ≡-refl) .left-eq .eqfun < x > = (liftS ≤-refl , liftS ≤-refl) , liftS ≤-refl , liftS ≤-refl

add-mor : (ℚ-intv ⊗ ℚ-intv) C.⇒ ℚ-intv
add-mor .idxf .prop-setoid._⇒_.func (q₁ , q₂) = q₁ + q₂
add-mor .idxf .prop-setoid._⇒_.func-resp-≈ (liftS ≡-refl , liftS ≡-refl) = liftS ≡-refl
add-mor .famf .transf (q₁ , q₂) = add-intervalG q₁ q₂
add-mor .famf .natural {q₁ , q₂} {q₁' , q₂'} (liftS ≡-refl , liftS ≡-refl) .right-eq .eqfun (bottom , bottom) = tt , tt
add-mor .famf .natural {q₁ , q₂} {q₁' , q₂'} (liftS ≡-refl , liftS ≡-refl) .right-eq .eqfun (bottom , < x >) = tt , tt
add-mor .famf .natural {q₁ , q₂} {q₁' , q₂'} (liftS ≡-refl , liftS ≡-refl) .right-eq .eqfun (< x > , bottom) = tt , tt
add-mor .famf .natural {q₁ , q₂} {q₁' , q₂'} (liftS ≡-refl , liftS ≡-refl) .right-eq .eqfun (< x > , < x₁ >) = (liftS ≤-refl , liftS ≤-refl) , liftS ≤-refl , liftS ≤-refl
add-mor .famf .natural {q₁ , q₂} {q₁' , q₂'} (liftS ≡-refl , liftS ≡-refl) .left-eq .eqfun bottom = (tt , tt) , tt , tt
add-mor .famf .natural {q₁ , q₂} {q₁' , q₂'} (liftS ≡-refl , liftS ≡-refl) .left-eq .eqfun < x > = ((liftS ≤-refl , liftS ≤-refl) , liftS ≤-refl , liftS ≤-refl) , (liftS ≤-refl , liftS ≤-refl) , liftS ≤-refl , liftS ≤-refl

zero : 𝟙 C.⇒ ℚ-intv
zero .idxf .prop-setoid._⇒_.func _ = 0ℚ
zero .idxf .prop-setoid._⇒_.func-resp-≈ _ = liftS ≡-refl
zero .famf .transf _ ._⇒g_.right ._=>_.fun _ = < record { lower = 0ℚ ; upper = 0ℚ ; l≤q = liftS ≤-refl ; q≤u = liftS ≤-refl } >
zero .famf .transf _ ._⇒g_.right ._=>_.mono _ = liftS ≤-refl , liftS ≤-refl
zero .famf .transf _ ._⇒g_.left ._=>_.fun _ = tt
zero .famf .transf _ ._⇒g_.left ._=>_.mono _ = tt
zero .famf .transf _ ._⇒g_.left⊣right {tt} {y} .proj₁ _ = tt
zero .famf .transf _ ._⇒g_.left⊣right {tt} {bottom} .proj₂ _ = tt
zero .famf .transf _ ._⇒g_.left⊣right {tt} {< x >} .proj₂ _ = x .l≤q , x .q≤u
zero .famf .natural e .right-eq .eqfun _ = (liftS ≤-refl , liftS ≤-refl) , liftS ≤-refl , liftS ≤-refl
zero .famf .natural e .left-eq .eqfun _ = tt , tt

{-
------------------------------------------------------------------------------
-- Negation

neg-right : ∀ q → Intv q → Intv (- q)
neg-right q x .lower = - (x .upper)
neg-right q x .upper = - (x .lower)
neg-right q x .l≤q = neg-antimono-≤ (x .q≤u)
neg-right q x .q≤u = neg-antimono-≤ (x .l≤q)

neg-left : ∀ q → Intv (- q) → Intv q
neg-left q x .lower = - (x .upper)
neg-left q x .upper = - (x .lower)
neg-left q x .l≤q = ≤-trans (neg-antimono-≤ (x .q≤u)) (≤-reflexive {!!})
neg-left q x .q≤u = ≤-trans (≤-reflexive {!!}) (neg-antimono-≤ (x .l≤q))

------------------------------------------------------------------------------
-- Scaling
module _ (r : ℚ) {{_ : Positive r}} where

  instance r≥0 = pos⇒nonNeg r
  instance r≠0 = pos⇒nonZero r

  scale-right : ∀ q → Intv q → Intv (r * q)
  scale-right q x .lower = r * x .lower
  scale-right q x .upper = r * x .upper
  scale-right q x .l≤q = *-monoˡ-≤-nonNeg r (x .l≤q)
  scale-right q x .q≤u = *-monoˡ-≤-nonNeg r (x .q≤u)

  scale-left : ∀ q → Intv (r * q) → Intv q
  scale-left q x .lower = x .lower ÷ r
  scale-left q x .upper = x .upper ÷ r
  scale-left q x .l≤q = {!!}
  scale-left q x .q≤u = {!!}

  scale-galois₁ : ∀ q x y → y ⊑ scale-right q x → scale-left q y ⊑ x
  scale-galois₁ q x y (liftS ϕ₁ , liftS ϕ₂) =
    (liftS {!!}) ,
    (liftS {!!})


-}
