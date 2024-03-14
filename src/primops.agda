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
strict-both-fwd ._=>M_.monotone {bottom , bottom} {bottom , < tt >} _ = tt
strict-both-fwd ._=>M_.monotone {bottom , bottom} {< tt > , bottom} _ = tt
strict-both-fwd ._=>M_.monotone {bottom , bottom} {< tt > , < tt >} _ = tt
strict-both-fwd ._=>M_.monotone {bottom , < tt >} {bottom , < tt >} _ = tt
strict-both-fwd ._=>M_.monotone {bottom , < tt >} {< tt > , < tt >} _ = tt
strict-both-fwd ._=>M_.monotone {< tt > , bottom} {< tt > , bottom} _ = tt
strict-both-fwd ._=>M_.monotone {< tt > , bottom} {< tt > , < tt >} _ = tt
strict-both-fwd ._=>M_.monotone {< tt > , < tt >} {< tt > , < tt >} _ = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , bottom} {bottom , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , bottom} {bottom , < tt >} = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , bottom} {< tt > , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , bottom} {< tt > , < tt >} = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , < tt >} {bottom , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , < tt >} {bottom , < tt >} = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , < tt >} {< tt > , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {bottom , < tt >} {< tt > , < tt >} = tt
strict-both-fwd ._=>M_.∧-preserving {< tt > , bottom} {bottom , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {< tt > , bottom} {bottom , < tt >} = tt
strict-both-fwd ._=>M_.∧-preserving {< tt > , bottom} {< tt > , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {< tt > , bottom} {< tt > , < tt >} = tt
strict-both-fwd ._=>M_.∧-preserving {< tt > , < tt >} {bottom , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {< tt > , < tt >} {bottom , < tt >} = tt
strict-both-fwd ._=>M_.∧-preserving {< tt > , < tt >} {< tt > , bottom} = tt
strict-both-fwd ._=>M_.∧-preserving {< tt > , < tt >} {< tt > , < tt >} = tt
strict-both-fwd ._=>M_.⊤-preserving = tt

strict-both-bwd : LJ 𝟙J =>J (LJ 𝟙J ⊕J LJ 𝟙J)
strict-both-bwd ._=>J_.func bottom = bottom , bottom
strict-both-bwd ._=>J_.func < tt > = < tt > , < tt >
strict-both-bwd ._=>J_.monotone {bottom} {bottom} _ = tt , tt
strict-both-bwd ._=>J_.monotone {bottom} {< x >} _ = tt , tt
strict-both-bwd ._=>J_.monotone {< tt >} {bottom} ()
strict-both-bwd ._=>J_.monotone {< tt >} {< tt >} tt = tt , tt
strict-both-bwd ._=>J_.∨-preserving {bottom} {bottom} = tt , tt
strict-both-bwd ._=>J_.∨-preserving {bottom} {< tt >} = tt , tt
strict-both-bwd ._=>J_.∨-preserving {< tt >} {bottom} = tt , tt
strict-both-bwd ._=>J_.∨-preserving {< tt >} {< tt >} = tt , tt
strict-both-bwd ._=>J_.⊥-preserving = tt , tt

-- a few other variants are possible, e.g. being 'strict' in second argument instead, or the degenerate
-- approximation which is constantly top in fwd direction and constantly bottom in bwd direction
