{-# OPTIONS --postfix-projections --prop --safe #-}

module matrix where

open import Level using (Level; _⊔_; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
