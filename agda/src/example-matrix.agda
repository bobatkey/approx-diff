{-# OPTIONS --prop --postfix-projections --safe #-}

module example-matrix where

open import Level using (0ℓ)
open import categories using (Category; HasTerminal; HasInitial; IsInitial; IsTerminal)

import join-semilattice-category as SemiLat
import cmon-enriched as CMon

open Category SemiLat.cat

TWO : SemiLat.Obj
TWO = SemiLat.TWO

open import two using (Two; O; I)
open import prop-setoid using (module ≈-Reasoning)
import join-semilattice
import preorder
open SemiLat._≃m_
open SemiLat._⇒_
open join-semilattice._≃m_ using (eqfunc)
open preorder._≃m_ using (eqfun)

scalar-comm : ∀ (f g : TWO ⇒ TWO) → (f ∘ g) ≈ (g ∘ f)
scalar-comm f g .f≃f .eqfunc .eqfun O =
  begin
    fun f (fun g O)
  ≈⟨ resp-≃ f (⊥-preserving-≃ g) ⟩
    fun f O
  ≈⟨ ⊥-preserving-≃ f ⟩
    O
  ≈˘⟨ ⊥-preserving-≃ g ⟩
    fun g O
  ≈˘⟨ resp-≃ g (⊥-preserving-≃ f) ⟩
    fun g (fun f O)
  ∎ where open ≈-Reasoning two.isEquivalence
scalar-comm f g .f≃f .eqfunc .eqfun I = go (fun f I) (fun g I) two.≃-refl two.≃-refl
  where
    open ≈-Reasoning two.isEquivalence

    step : ∀ (a b : Two) → a two.≃ fun f I → b two.≃ fun g I → fun f b two.≃ fun g a
    step O O _     _     = begin fun f O ≈⟨ ⊥-preserving-≃ f ⟩ O ≈˘⟨ ⊥-preserving-≃ g ⟩ fun g O ∎
    step O I eq-a  _     = begin fun f I ≈˘⟨ eq-a ⟩ O ≈˘⟨ ⊥-preserving-≃ g ⟩ fun g O ∎
    step I O _     eq-b  = begin fun f O ≈⟨ ⊥-preserving-≃ f ⟩ O ≈⟨ eq-b ⟩ fun g I ∎
    step I I eq-a  eq-b  = begin fun f I ≈˘⟨ eq-a ⟩ I ≈⟨ eq-b ⟩ fun g I ∎

    go : ∀ (a b : Two) → a two.≃ fun f I → b two.≃ fun g I → fun f (fun g I) two.≃ fun g (fun f I)
    go a b eq-a eq-b =
      begin
        fun f (fun g I)
      ≈⟨ resp-≃ f (two.≃-sym eq-b) ⟩
        fun f b
      ≈⟨ step a b eq-a eq-b ⟩
        fun g a
      ≈⟨ resp-≃ g eq-a ⟩
        fun g (fun f I)
      ∎

open CMon.CMonEnriched SemiLat.cmon-enriched using (_+m_)

import matrices
open matrices SemiLat.cmon-enriched
  (CMon.cmon+products→biproducts SemiLat.cmon-enriched SemiLat.products)
  (HasTerminal.witness SemiLat.terminal)
  (HasInitial.is-initial SemiLat.initial)
  (HasTerminal.is-terminal SemiLat.terminal)
  TWO
  scalar-comm

private
  module Mat = Category cat

open categories using (HasProducts)

import example-signature-interpretation
unit : Mat._⇒_ 0 2
unit = HasInitial.from-initial initial {2}

conjunct : Mat._⇒_ (HasProducts.prod products 2 2) 2
conjunct = HasProducts.p₁ products {2} {2} +m HasProducts.p₂ products {2} {2}

open example-signature-interpretation cat products terminal 2 unit conjunct
