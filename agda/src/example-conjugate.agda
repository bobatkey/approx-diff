{-# OPTIONS --prop --postfix-projections --safe #-}

module example-conjugate where

open import Level using (0ℓ; lift)
open import Data.List using (List; []; _∷_)
open import every using (Every; []; _∷_)
open import signature
import language-syntax
import label
import conjugate

open import example-signature

module L = language-syntax Sig

import indexed-family
import join-semilattice-category
import join-semilattice
import preorder
import prop-setoid

open import two renaming (I to ⊤; O to ⊥)
open import Data.Unit renaming (tt to ·; ⊤ to Unit) using ()
open import Data.Product using (_,_; _×_; proj₁; proj₂)

open prop-setoid.Setoid

open L hiding (_,_)

import example

open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

module example1 where
  open import ho-model
  open import example-signature-interpretation conjugate.cat conjugate.products conjugate.terminal conjugate.TWO conjugate.unit conjugate.conjunct
  open Conjugate.interp Sig BaseInterp1

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0) , (label.b , 1) , (label.a , 1) , _

  -- bwd-slice behaves the same as in the Galois examples, but fwd-slice does not
  fwd-slice : _ → _
  fwd-slice supply = ⟦ example.ex.query label.a ⟧tm .famf .transf (_ , input) .proj₁ .*→* .func .fun (· , supply)
    where
      open indexed-family._⇒f_
      open join-semilattice-category._⇒_
      open join-semilattice._=>_
      open preorder._=>_

  -- Output depends on 1st label (would be ⊥ in the Galois example)
  test-1 : fwd-slice ((· , ⊤) , (· , ⊥) , (· , ⊥) , _) ≡ ⊤
  test-1 = ≡-refl

  -- Output doesn't depend on 2nd label
  test-2 : fwd-slice ((· , ⊥) , (· , ⊤) , (· , ⊥) , _) ≡ ⊥
  test-2 = ≡-refl

  -- Output depends on 3rd label (would be ⊥ in the Galois example)
  test-3 : fwd-slice ((· , ⊥) , (· , ⊥) , (· , ⊤) , _) ≡ ⊤
  test-3 = ≡-refl
