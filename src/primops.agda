{-# OPTIONS --postfix-projections --without-K --safe #-}

module primops where

open import Data.Unit using (tt)
open import Data.Product using (_,_)

open import join-semilattice
  renaming (_=>_ to _=>J_; 𝟙 to 𝟙J; _⊕_ to _⊕J_; L to LJ)
open import meet-semilattice
  renaming (_=>_ to _=>M_; 𝟙 to 𝟙M; _⊕_ to _⊕M_; L to LM)
open MeetSemilattice renaming (_≤_ to _≤M_)

strict-both-fwd : (LM 𝟙M ⊕M LM 𝟙M) =>M LM 𝟙M
strict-both-fwd ._=>M_.func (bottom , bottom) = bottom
strict-both-fwd ._=>M_.func (bottom , < tt >) = bottom
strict-both-fwd ._=>M_.func (< tt > , bottom) = bottom
strict-both-fwd ._=>M_.func (< tt > , < tt >) = < tt >
strict-both-fwd ._=>M_.monotone {bottom , bottom} {bottom , bottom} _ = tt
strict-both-fwd ._=>M_.monotone {bottom , bottom} {bottom , < x >} _ = tt
strict-both-fwd ._=>M_.monotone {bottom , bottom} {< x > , bottom} _ = tt
strict-both-fwd ._=>M_.monotone {bottom , bottom} {< x > , < x₁ >} _ = tt
strict-both-fwd ._=>M_.monotone {bottom , < x >} {bottom , < x₁ >} _ = tt
strict-both-fwd ._=>M_.monotone {bottom , < x >} {< x₁ > , < x₂ >} _ = tt
strict-both-fwd ._=>M_.monotone {< x > , bottom} {< x₁ > , bottom} _ = tt
strict-both-fwd ._=>M_.monotone {< x > , bottom} {< x₁ > , < x₂ >} _ = tt
strict-both-fwd ._=>M_.monotone {< x > , < x₁ >} {< x₂ > , < x₃ >} _ = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , bottom} {bottom , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , bottom} {bottom , < x >} = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , bottom} {< x > , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , bottom} {< x > , < x₁ >} = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , < x >} {bottom , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , < x >} {bottom , < x₁ >} = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , < x >} {< x₁ > , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , < x >} {< x₁ > , < x₂ >} = tt
strict-both-fwd ._=>M_.∧-preserving {< x > , bottom} {bottom , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {< x > , bottom} {bottom , < x₁ >} = tt
strict-both-fwd ._=>M_.∧-preserving {< x > , bottom} {< x₁ > , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {< x > , bottom} {< x₁ > , < x₂ >} = tt
strict-both-fwd ._=>M_.∧-preserving {< x > , < x₁ >} {bottom , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {< x > , < x₁ >} {bottom , < x₂ >} = tt
strict-both-fwd ._=>M_.∧-preserving {< x > , < x₁ >} {< x₂ > , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {< x > , < x₁ >} {< x₂ > , < x₃ >} = tt
strict-both-fwd ._=>M_.⊤-preserving = tt

strict-both-bwd : LJ 𝟙J =>J (LJ 𝟙J ⊕J LJ 𝟙J)
strict-both-bwd ._=>J_.func _ = bottom , bottom
strict-both-bwd ._=>J_.monotone _ = tt , tt
strict-both-bwd ._=>J_.∨-preserving = tt , tt
strict-both-bwd ._=>J_.⊥-preserving = tt , tt
