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
    step : ∀ (a b : Two) → a two.≃ fun f I → b two.≃ fun g I → fun f b two.≃ fun g a
    step O O _   _ = two.≃-trans (⊥-preserving-≃ f) (two.≃-sym (⊥-preserving-≃ g))
    step O I eq-a _ = two.≃-trans (two.≃-sym eq-a) (two.≃-sym (⊥-preserving-≃ g))
    step I O _ eq-b = two.≃-trans (⊥-preserving-≃ f) eq-b
    step I I eq-a eq-b = two.≃-trans (two.≃-sym eq-a) eq-b

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
      ∎ where open ≈-Reasoning two.isEquivalence

import matrices
open matrices SemiLat.cmon-enriched
  (CMon.cmon+products→biproducts SemiLat.cmon-enriched SemiLat.products)
  (HasTerminal.witness SemiLat.terminal)
  (HasInitial.is-initial SemiLat.initial)
  (HasTerminal.is-terminal SemiLat.terminal)
  TWO
  scalar-comm
