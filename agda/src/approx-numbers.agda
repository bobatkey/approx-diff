{-# OPTIONS --postfix-projections --prop --safe #-}

module approx-numbers where

open import Level using (0ℓ; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import prop using (⊤; tt; ⊥; LiftS; liftS; _∧_; _,_; proj₁; proj₂)
open import prop-setoid using (Setoid; IsEquivalence)
open import preorder using (Preorder; _=>_; bottom; <_>)
open import meet-semilattice using (MeetSemilattice)
open import join-semilattice using (JoinSemilattice)
open import basics using (IsPreorder; IsMeet; IsTop; IsJoin; IsBottom)

open import categories using (HasTerminal; Category)
open import galois using (Obj; _⊕_; _⇒g_)

import fam

open import Data.Rational using (ℚ; _≤_; _⊔_; _⊓_; _+_; _-_; 0ℚ; -_; Positive; _*_; _÷_; NonZero)
open import Data.Rational.Properties using (≤-refl; ≤-trans; ⊓-glb; ⊔-lub; p⊓q≤p; p⊓q≤q; +-mono-≤; module ≤-Reasoning; +-comm; ≤-reflexive; +-assoc; +-inverseʳ; +-inverseˡ; +-identityʳ; +-identityˡ; ⊓-mono-≤; p≤p⊔q; p≤q⊔p; neg-antimono-≤; pos⇒nonZero; pos⇒nonNeg; *-monoˡ-≤-nonNeg; ⊔-mono-≤)
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


-- ≤-trans (adjoint₂ {y} { - x} {z} (≤-trans (≤-reflexive (+-comm y (- (- x)))) (≤-trans (+-mono-≤ {!!} (≤-refl {y})) ϕ))) (≤-reflexive (+-comm (- x) z))

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
  no-eta-equality
  field
    lower : ℚ
    upper : ℚ
    l≤q   : lower ≤ q
    q≤u   : q ≤ upper
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
(x ⊓I y) .l≤q = ≤-trans (p⊓q≤p _ _) (x .l≤q)
(x ⊓I y) .q≤u = ≤-trans (x .q≤u) (p≤p⊔q _ _)

⊤I : ∀ {q} → Intv q
⊤I {q} .lower = q
⊤I {q} .upper = q
⊤I {q} .l≤q = ≤-refl
⊤I {q} .q≤u = ≤-refl

⊤I-isTop : ∀ {q} → IsTop (⊑I-isPreorder {q}) ⊤I
⊤I-isTop .IsTop.≤-top {x} = liftS (x .l≤q) , liftS (x .q≤u)

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
(x ⊔I y) .l≤q = ⊔-lub (x .l≤q) (y .l≤q)
(x ⊔I y) .q≤u = ⊓-glb (x .q≤u) (y .q≤u)

⊔I-isJoin : ∀ {q} → IsJoin (⊑I-isPreorder {q}) _⊔I_
⊔I-isJoin .IsJoin.inl = liftS (p≤p⊔q _ _) , liftS (p⊓q≤p _ _)
⊔I-isJoin .IsJoin.inr {x} = liftS (p≤q⊔p (x .lower) _) , liftS (p⊓q≤q (x .upper) _)
⊔I-isJoin .IsJoin.[_,_] (liftS ϕ₁ , liftS ϕ₂) (liftS ψ₁ , liftS ψ₂) =
  liftS (⊔-lub ϕ₁ ψ₁) , liftS (⊓-glb ϕ₂ ψ₂)

------------------------------------------------------------------------------
-- Addition

add-right : ∀ q₁ q₂ → Intv q₁ → Intv q₂ → Intv (q₁ + q₂)
add-right q₁ q₂ x y .lower = (q₂ + x .lower) ⊓ (q₁ + y .lower)
add-right q₁ q₂ x y .upper = (q₂ + x .upper) ⊔ (q₁ + y .upper)
add-right q₁ q₂ x y .l≤q = ≤-trans (p⊓q≤q (q₂ + x .lower) (q₁ + y .lower)) (+-mono-≤ (≤-refl {q₁}) (y .l≤q))
add-right q₁ q₂ x y .q≤u = ≤-trans (+-mono-≤ (≤-refl {q₁}) (y .q≤u)) (p≤q⊔p (q₂ + x .upper) _)

add-left : ∀ q₁ q₂ → Intv (q₁ + q₂) → Intv q₁ × Intv q₂
add-left q₁ q₂ x .proj₁ .lower = x .lower - q₂
add-left q₁ q₂ x .proj₁ .upper = x .upper - q₂
add-left q₁ q₂ x .proj₁ .l≤q = adjoint₁ {x .lower} {q₂} {q₁} (≤-trans (x .l≤q) (≤-reflexive (+-comm q₁ q₂)))
add-left q₁ q₂ x .proj₁ .q≤u = adjoint₂' {q₂} {q₁} {x .upper} (≤-trans (≤-reflexive (+-comm q₂ q₁)) (x .q≤u))
add-left q₁ q₂ x .proj₂ .lower = x .lower - q₁
add-left q₁ q₂ x .proj₂ .upper = x .upper - q₁
add-left q₁ q₂ x .proj₂ .l≤q = adjoint₁ {x .lower} {q₁} {q₂} (x .l≤q)
add-left q₁ q₂ x .proj₂ .q≤u = adjoint₂' {q₁} {q₂} {x .upper} (x .q≤u)

galois₁ : ∀ q₁ q₂ x y z →
          z ⊑ (add-right q₁ q₂ x y) → (add-left q₁ q₂ z .proj₁ ⊑ x) ∧ (add-left q₁ q₂ z .proj₂ ⊑ y)
galois₁ q₁ q₂ x y z (liftS ϕ₁ , liftS ϕ₂) .proj₁ =
  liftS (adjoint₁ {z .lower} {q₂} {x .lower} (≤-trans ϕ₁ (p⊓q≤p _ _))) ,
  liftS (adjoint₂' {q₂} {x .upper} {z .upper} (≤-trans (p≤p⊔q (q₂ + x .upper) (q₁ + y .upper)) ϕ₂))
galois₁ q₁ q₂ x y z (liftS ϕ₁ , liftS ϕ₂) .proj₂ =
  liftS (adjoint₁ {z .lower} {q₁} {y .lower} (≤-trans ϕ₁ (p⊓q≤q (q₂ + x .lower) _))) ,
  liftS (adjoint₂' {q₁} {y .upper} {z .upper} (≤-trans (p≤q⊔p (q₂ + x .upper) (q₁ + y .upper)) ϕ₂))

galois₂ : ∀ q₁ q₂ x y z →
          (add-left q₁ q₂ z .proj₁ ⊑ x) ∧ (add-left q₁ q₂ z .proj₂ ⊑ y) → z ⊑ (add-right q₁ q₂ x y)
galois₂ q₁ q₂ x y z ((liftS ϕ₁ , liftS ϕ₂) , (liftS ψ₁ , liftS ψ₂)) =
  liftS (⊓-glb (adjoint₂ ϕ₁) (adjoint₂ ψ₁)) ,
  liftS (⊔-lub (adjoint₁' ϕ₂) (adjoint₁' ψ₂))

add-right-mono : ∀ q₁ q₂ {x₁ x₂ y₁ y₂} →
                 x₁ ⊑ x₂ → y₁ ⊑ y₂ →
                 add-right q₁ q₂ x₁ y₁ ⊑ add-right q₁ q₂ x₂ y₂
add-right-mono q₁ q₂ (liftS ϕ₁ , liftS ϕ₂) (liftS ψ₁ , liftS ψ₂) =
  (liftS (⊓-mono-≤ (+-mono-≤ (≤-refl {q₂}) ϕ₁) (+-mono-≤ (≤-refl {q₁}) ψ₁))) ,
  (liftS (⊔-mono-≤ (+-mono-≤ (≤-refl {q₂}) ϕ₂) (+-mono-≤ (≤-refl {q₁}) ψ₂)))

------------------------------------------------------------------------------
Interval : ℚ → Obj
Interval q .galois.Obj.carrier = preorder.L (IntvPreorder q)
Interval q .galois.Obj.meets = meet-semilattice.L (meets q)
Interval q .galois.Obj.joins = join-semilattice.L₀ ⊔I-isJoin

add-interval : ∀ q₁ q₂ → (Interval q₁ ⊕ Interval q₂) ⇒g Interval (q₁ + q₂)
add-interval q₁ q₂ ._⇒g_.right ._=>_.fun (bottom , bottom) = bottom
add-interval q₁ q₂ ._⇒g_.right ._=>_.fun (bottom , < x >) = bottom
add-interval q₁ q₂ ._⇒g_.right ._=>_.fun (< x > , bottom) = bottom
add-interval q₁ q₂ ._⇒g_.right ._=>_.fun (< x > , < y >) = < add-right q₁ q₂ x y >
add-interval q₁ q₂ ._⇒g_.right ._=>_.mono {bottom , bottom} {x₂ , y₂} ϕ = tt
add-interval q₁ q₂ ._⇒g_.right ._=>_.mono {bottom , < x >} {x₂ , y₂} ϕ = tt
add-interval q₁ q₂ ._⇒g_.right ._=>_.mono {< x > , bottom} {x₂ , y₂} ϕ = tt
add-interval q₁ q₂ ._⇒g_.right ._=>_.mono {< x₁ > , < y₁ >} {< x₂ > , < y₂ >} (x₁≤x₂ , y₁≤y₂) =
  add-right-mono q₁ q₂ {x₁} {x₂} {y₁} {y₂} x₁≤x₂ y₁≤y₂
add-interval q₁ q₂ ._⇒g_.left ._=>_.fun bottom = bottom , bottom
add-interval q₁ q₂ ._⇒g_.left ._=>_.fun < x > = < add-left q₁ q₂ x .proj₁ > , < add-left q₁ q₂ x .proj₂ >
add-interval q₁ q₂ ._⇒g_.left ._=>_.mono {bottom} {y} ϕ = tt , tt
add-interval q₁ q₂ ._⇒g_.left ._=>_.mono {< x >} {< y >} (liftS ϕ₁ , liftS ϕ₂) .proj₁ =
  (liftS (+-mono-≤ ϕ₁ ≤-refl)) ,
  (liftS (+-mono-≤ ϕ₂ ≤-refl))
add-interval q₁ q₂ ._⇒g_.left ._=>_.mono {< x >} {< y >} (liftS ϕ₁ , liftS ϕ₂) .proj₂ =
  (liftS (+-mono-≤ ϕ₁ ≤-refl)) ,
  (liftS (+-mono-≤ ϕ₂ ≤-refl))
add-interval q₁ q₂ ._⇒g_.left⊣right {bottom , bottom} {bottom} = (λ _ → tt , tt) , (λ _ → tt)
add-interval q₁ q₂ ._⇒g_.left⊣right {bottom , bottom} {< x >} = (λ ()) , λ ()
add-interval q₁ q₂ ._⇒g_.left⊣right {bottom , < y >} {bottom} = (λ _ → tt , tt) , (λ _ → tt)
add-interval q₁ q₂ ._⇒g_.left⊣right {bottom , < y >} {< z >} = (λ ()) , (λ ())
add-interval q₁ q₂ ._⇒g_.left⊣right {< x > , bottom} {bottom} = (λ _ → tt , tt) , (λ _ → tt)
add-interval q₁ q₂ ._⇒g_.left⊣right {< x > , bottom} {< z >} = (λ ()) , (λ ())
add-interval q₁ q₂ ._⇒g_.left⊣right {< x > , < y >} {bottom} = (λ _ → tt , tt) , (λ _ → tt)
add-interval q₁ q₂ ._⇒g_.left⊣right {< x > , < y >} {< z >} .proj₁ = galois₁ q₁ q₂ x y z
add-interval q₁ q₂ ._⇒g_.left⊣right {< x > , < y >} {< z >} .proj₂ = galois₂ q₁ q₂ x y z

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
subst-Intv q₁ q₂ eq x .l≤q = {!!}
subst-Intv q₁ q₂ eq x .q≤u = {!!}

subst-Interval : ∀ q₁ q₂ → LiftS 0ℓ (q₁ ≡ q₂) → Interval q₁ ⇒g Interval q₂
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
ℚ-intv .fam .fm = Interval
ℚ-intv .fam .subst eq = subst-Interval _ _ eq
ℚ-intv .fam .refl* .right-eq .eqfun bottom = tt , tt
ℚ-intv .fam .refl* .right-eq .eqfun < x > = (liftS ≤-refl , liftS ≤-refl) , liftS ≤-refl , liftS ≤-refl
ℚ-intv .fam .refl* .left-eq .eqfun bottom = tt , tt
ℚ-intv .fam .refl* .left-eq .eqfun < x > = (liftS ≤-refl , liftS ≤-refl) , liftS ≤-refl , liftS ≤-refl
ℚ-intv .fam .trans* (liftS ≡-refl) (liftS ≡-refl) .right-eq .eqfun bottom = tt , tt
ℚ-intv .fam .trans* (liftS ≡-refl) (liftS ≡-refl) .right-eq .eqfun < x > = (liftS ≤-refl , liftS ≤-refl) , liftS ≤-refl , liftS ≤-refl
ℚ-intv .fam .trans* (liftS ≡-refl) (liftS ≡-refl) .left-eq .eqfun bottom = tt , tt
ℚ-intv .fam .trans* (liftS ≡-refl) (liftS ≡-refl) .left-eq .eqfun < x > = (liftS ≤-refl , liftS ≤-refl) , liftS ≤-refl , liftS ≤-refl

add : (ℚ-intv ⊗ ℚ-intv) C.⇒ ℚ-intv
add .idxf .prop-setoid._⇒_.func (q₁ , q₂) = q₁ + q₂
add .idxf .prop-setoid._⇒_.func-resp-≈ (liftS ≡-refl , liftS ≡-refl) = liftS ≡-refl
add .famf .transf (q₁ , q₂) = add-interval q₁ q₂
add .famf .natural {q₁ , q₂} {q₁' , q₂'} (liftS ≡-refl , liftS ≡-refl) .right-eq .eqfun (bottom , bottom) = tt , tt
add .famf .natural {q₁ , q₂} {q₁' , q₂'} (liftS ≡-refl , liftS ≡-refl) .right-eq .eqfun (bottom , < x >) = tt , tt
add .famf .natural {q₁ , q₂} {q₁' , q₂'} (liftS ≡-refl , liftS ≡-refl) .right-eq .eqfun (< x > , bottom) = tt , tt
add .famf .natural {q₁ , q₂} {q₁' , q₂'} (liftS ≡-refl , liftS ≡-refl) .right-eq .eqfun (< x > , < x₁ >) = (liftS ≤-refl , liftS ≤-refl) , liftS ≤-refl , liftS ≤-refl
add .famf .natural {q₁ , q₂} {q₁' , q₂'} (liftS ≡-refl , liftS ≡-refl) .left-eq .eqfun bottom = (tt , tt) , tt , tt
add .famf .natural {q₁ , q₂} {q₁' , q₂'} (liftS ≡-refl , liftS ≡-refl) .left-eq .eqfun < x > = ((liftS ≤-refl , liftS ≤-refl) , liftS ≤-refl , liftS ≤-refl) ,
                                                                                                (liftS ≤-refl , liftS ≤-refl) , liftS ≤-refl , liftS ≤-refl

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
