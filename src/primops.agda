{-# OPTIONS --postfix-projections --without-K --safe #-}

module primops where

open import Data.Unit using (tt)
open import Data.Product using (_,_)

open import join-semilattice
  renaming (_=>_ to _=>J_; 𝟙 to 𝟙J; _⊕_ to _⊕J_; L to LJ)
open import meet-semilattice
  renaming (_=>_ to _=>M_; 𝟙 to 𝟙M; _⊕_ to _⊕M_; L to LM)
open MeetSemilattice renaming (_≤_ to _≤M_)

use-both-fwd : (LM 𝟙M ⊕M LM 𝟙M) =>M LM 𝟙M
use-both-fwd ._=>M_.func (bottom , bottom) = bottom
use-both-fwd ._=>M_.func (bottom , < tt >) = bottom
use-both-fwd ._=>M_.func (< tt > , bottom) = bottom
use-both-fwd ._=>M_.func (< tt > , < tt >) = < tt >
use-both-fwd ._=>M_.monotone {bottom , bottom} {bottom , bottom} _ = tt
use-both-fwd ._=>M_.monotone {bottom , bottom} {bottom , < tt >} _ = tt
use-both-fwd ._=>M_.monotone {bottom , bottom} {< tt > , bottom} _ = tt
use-both-fwd ._=>M_.monotone {bottom , bottom} {< tt > , < tt >} _ = tt
use-both-fwd ._=>M_.monotone {bottom , < tt >} {bottom , < tt >} _ = tt
use-both-fwd ._=>M_.monotone {bottom , < tt >} {< tt > , < tt >} _ = tt
use-both-fwd ._=>M_.monotone {< tt > , bottom} {< tt > , bottom} _ = tt
use-both-fwd ._=>M_.monotone {< tt > , bottom} {< tt > , < tt >} _ = tt
use-both-fwd ._=>M_.monotone {< tt > , < tt >} {< tt > , < tt >} _ = tt
use-both-fwd ._=>M_.∧-preserving {bottom , bottom} {bottom , bottom} = tt
use-both-fwd ._=>M_.∧-preserving {bottom , bottom} {bottom , < tt >} = tt
use-both-fwd ._=>M_.∧-preserving {bottom , bottom} {< tt > , bottom} = tt
use-both-fwd ._=>M_.∧-preserving {bottom , bottom} {< tt > , < tt >} = tt
use-both-fwd ._=>M_.∧-preserving {bottom , < tt >} {bottom , bottom} = tt
use-both-fwd ._=>M_.∧-preserving {bottom , < tt >} {bottom , < tt >} = tt
use-both-fwd ._=>M_.∧-preserving {bottom , < tt >} {< tt > , bottom} = tt
use-both-fwd ._=>M_.∧-preserving {bottom , < tt >} {< tt > , < tt >} = tt
use-both-fwd ._=>M_.∧-preserving {< tt > , bottom} {bottom , bottom} = tt
use-both-fwd ._=>M_.∧-preserving {< tt > , bottom} {bottom , < tt >} = tt
use-both-fwd ._=>M_.∧-preserving {< tt > , bottom} {< tt > , bottom} = tt
use-both-fwd ._=>M_.∧-preserving {< tt > , bottom} {< tt > , < tt >} = tt
use-both-fwd ._=>M_.∧-preserving {< tt > , < tt >} {bottom , bottom} = tt
use-both-fwd ._=>M_.∧-preserving {< tt > , < tt >} {bottom , < tt >} = tt
use-both-fwd ._=>M_.∧-preserving {< tt > , < tt >} {< tt > , bottom} = tt
use-both-fwd ._=>M_.∧-preserving {< tt > , < tt >} {< tt > , < tt >} = tt
use-both-fwd ._=>M_.⊤-preserving = tt

use-both-bwd : LJ 𝟙J =>J (LJ 𝟙J ⊕J LJ 𝟙J)
use-both-bwd ._=>J_.func bottom = bottom , bottom
use-both-bwd ._=>J_.func < tt > = < tt > , < tt >
use-both-bwd ._=>J_.monotone {bottom} {bottom} _ = tt , tt
use-both-bwd ._=>J_.monotone {bottom} {< x >} _ = tt , tt
use-both-bwd ._=>J_.monotone {< tt >} {bottom} ()
use-both-bwd ._=>J_.monotone {< tt >} {< tt >} tt = tt , tt
use-both-bwd ._=>J_.∨-preserving {bottom} {bottom} = tt , tt
use-both-bwd ._=>J_.∨-preserving {bottom} {< tt >} = tt , tt
use-both-bwd ._=>J_.∨-preserving {< tt >} {bottom} = tt , tt
use-both-bwd ._=>J_.∨-preserving {< tt >} {< tt >} = tt , tt
use-both-bwd ._=>J_.⊥-preserving = tt , tt

use-fst-fwd : (LM 𝟙M ⊕M LM 𝟙M) =>M LM 𝟙M
use-fst-fwd ._=>M_.func (bottom , bottom) = bottom
use-fst-fwd ._=>M_.func (bottom , < tt >) = bottom
use-fst-fwd ._=>M_.func (< tt > , bottom) = < tt >
use-fst-fwd ._=>M_.func (< tt > , < tt >) = < tt >
use-fst-fwd ._=>M_.monotone {bottom , bottom} {bottom , bottom} _ = tt
use-fst-fwd ._=>M_.monotone {bottom , bottom} {bottom , < tt >} _ = tt
use-fst-fwd ._=>M_.monotone {bottom , bottom} {< tt > , bottom} _ = tt
use-fst-fwd ._=>M_.monotone {bottom , bottom} {< tt > , < tt >} _ = tt
use-fst-fwd ._=>M_.monotone {bottom , < tt >} {bottom , < tt >} _ = tt
use-fst-fwd ._=>M_.monotone {bottom , < tt >} {< tt > , < tt >} _ = tt
use-fst-fwd ._=>M_.monotone {< tt > , bottom} {< tt > , bottom} _ = tt
use-fst-fwd ._=>M_.monotone {< tt > , bottom} {< tt > , < tt >} _ = tt
use-fst-fwd ._=>M_.monotone {< tt > , < tt >} {< tt > , < tt >} _ = tt
use-fst-fwd ._=>M_.∧-preserving {bottom , bottom} {bottom , bottom} = tt
use-fst-fwd ._=>M_.∧-preserving {bottom , bottom} {bottom , < tt >} = tt
use-fst-fwd ._=>M_.∧-preserving {bottom , bottom} {< tt > , bottom} = tt
use-fst-fwd ._=>M_.∧-preserving {bottom , bottom} {< tt > , < tt >} = tt
use-fst-fwd ._=>M_.∧-preserving {bottom , < tt >} {bottom , bottom} = tt
use-fst-fwd ._=>M_.∧-preserving {bottom , < tt >} {bottom , < tt >} = tt
use-fst-fwd ._=>M_.∧-preserving {bottom , < tt >} {< tt > , bottom} = tt
use-fst-fwd ._=>M_.∧-preserving {bottom , < tt >} {< tt > , < tt >} = tt
use-fst-fwd ._=>M_.∧-preserving {< tt > , bottom} {bottom , bottom} = tt
use-fst-fwd ._=>M_.∧-preserving {< tt > , bottom} {bottom , < tt >} = tt
use-fst-fwd ._=>M_.∧-preserving {< tt > , bottom} {< tt > , bottom} = tt
use-fst-fwd ._=>M_.∧-preserving {< tt > , bottom} {< tt > , < tt >} = tt
use-fst-fwd ._=>M_.∧-preserving {< tt > , < tt >} {bottom , bottom} = tt
use-fst-fwd ._=>M_.∧-preserving {< tt > , < tt >} {bottom , < tt >} = tt
use-fst-fwd ._=>M_.∧-preserving {< tt > , < tt >} {< tt > , bottom} = tt
use-fst-fwd ._=>M_.∧-preserving {< tt > , < tt >} {< tt > , < tt >} = tt
use-fst-fwd ._=>M_.⊤-preserving = tt

use-fst-bwd : LJ 𝟙J =>J (LJ 𝟙J ⊕J LJ 𝟙J)
use-fst-bwd ._=>J_.func bottom = bottom , bottom
use-fst-bwd ._=>J_.func < tt > = < tt > , bottom
use-fst-bwd ._=>J_.monotone {bottom} {bottom} _ = tt , tt
use-fst-bwd ._=>J_.monotone {bottom} {< tt >} _ = tt , tt
use-fst-bwd ._=>J_.monotone {< tt >} {< tt >} _ = tt , tt
use-fst-bwd ._=>J_.∨-preserving {bottom} {bottom} = tt , tt
use-fst-bwd ._=>J_.∨-preserving {bottom} {< tt >} = tt , tt
use-fst-bwd ._=>J_.∨-preserving {< tt >} {bottom} = tt , tt
use-fst-bwd ._=>J_.∨-preserving {< tt >} {< tt >} = tt , tt
use-fst-bwd ._=>J_.⊥-preserving = tt , tt

-- a couple of other variants are possible, e.g. being 'strict' in second argument instead, or the
-- degenerate approximation which is constantly top in fwd direction and constantly bottom in bwd direction
