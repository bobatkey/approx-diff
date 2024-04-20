{-# OPTIONS --postfix-projections --safe --without-K #-}

module fo-approxset where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Level
open import basics
open import poset using (Poset; L)
open import meet-semilattice-2 renaming (_=>_ to _=>M_; id to idM; _∘_ to _∘M_; L to LM)
open import join-semilattice-2 renaming (_=>_ to _=>J_; id to idJ; _∘_ to _∘J_; L to LJ)

record FOApproxSet : Set (suc 0ℓ) where
  field
    elem    : Set
    approx : elem → Poset
    fapprox : (x : elem) → MeetSemilattice (approx x)
    rapprox : (x : elem) → JoinSemilattice (approx x)

open FOApproxSet

module _ where
  infix 4 _⇔_

  _⇔_ : Set → Set → Set
  P ⇔ Q = (P → Q) × (Q → P)

record _⇒_ (X Y : FOApproxSet) : Set where
  open _=>M_
  open Poset

  field
    func : X .elem → Y .elem
    fwd : (x : X .elem) → X .fapprox x =>M Y. fapprox (func x)
    bwd : (x : X .elem) → Y .rapprox (func x) =>J X .rapprox x
    bwd⊣fwd : ∀ (x : X .elem) {x' y'} →
              Y .approx (func x) ._≤_ y' (fwd x ._=>M_.func x') ⇔ X .approx x ._≤_ (bwd x ._=>J_.func y') x'

open _⇒_

-- Definitions for category

id : ∀ {X} → X ⇒ X
id .func x = x
id .fwd x = idM
id .bwd x = idJ
id .bwd⊣fwd x .proj₁ x'≤ = x'≤
id .bwd⊣fwd x .proj₂ ≤x' = ≤x'

_∘_ : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
(f ∘ g) .func x = f .func (g .func x)
(f ∘ g) .fwd x = f .fwd (g .func x) ∘M g .fwd x
(f ∘ g) .bwd x = g .bwd x ∘J f .bwd (g .func x)
(f ∘ g) .bwd⊣fwd x .proj₁ z'≤fgx' =
  g .bwd⊣fwd x .proj₁ (f .bwd⊣fwd (g .func x) .proj₁ z'≤fgx')
(f ∘ g) .bwd⊣fwd x .proj₂ gfz'≤x' =
  f .bwd⊣fwd (g .func x) .proj₂ (g .bwd⊣fwd x .proj₂ gfz'≤x')

infixr 10 _∘_

-- TODO: definitions for Cartesian closure

-- Lifting
module _ where

  ℒ : FOApproxSet → FOApproxSet
  ℒ X .elem = X .elem
  ℒ X .approx x = L (X .approx x)
  ℒ X .fapprox x = LM (X .fapprox x)
  ℒ X .rapprox x = LJ (X .rapprox x)
