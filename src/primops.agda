{-# OPTIONS --postfix-projections --without-K --safe #-}

module PrimOps where

open import Data.Unit using (tt)
open import Data.Product using (_,_)

open import join-semilattice
  renaming (_=>_ to _=>J_; 𝟙 to 𝟙J; _⊕_ to _⊕J_; L to LJ)
open import meet-semilattice
  renaming (_=>_ to _=>M_; 𝟙 to 𝟙M; _⊕_ to _⊕M_; L to LM)

plus-fwd : (LM 𝟙M ⊕M LM 𝟙M) =>M LM 𝟙M
plus-fwd ._=>M_.func _ = < tt >
plus-fwd ._=>M_.monotone _ = tt
plus-fwd ._=>M_.∧-preserving = tt
plus-fwd ._=>M_.⊤-preserving = tt

plus-bwd : LJ 𝟙J =>J (LJ 𝟙J ⊕J LJ 𝟙J)
plus-bwd ._=>J_.func _ = bottom , bottom
plus-bwd ._=>J_.monotone _ = tt , tt
plus-bwd ._=>J_.∨-preserving = tt , tt
plus-bwd ._=>J_.⊥-preserving = tt , tt
