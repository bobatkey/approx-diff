{-# OPTIONS --prop --postfix-projections --safe #-}

module example-matrix where

open import Level using (0ℓ)
open import categories using (Category; HasTerminal; HasInitial; IsInitial; IsTerminal; HasProducts)

import join-semilattice-category as SemiLat
import cmon-enriched as CMon
open CMon.CMonEnriched SemiLat.cmon-enriched using (_+m_)

import ho-model
open ho-model.Matrix

private
  module Cat = Category cat

import example-signature-interpretation
unit : Cat._⇒_ 0 1
unit = HasInitial.from-initial initial {1}

conjunct : Cat._⇒_ (HasProducts.prod products 1 1) 1
conjunct = HasProducts.p₁ products {1} {1} +m HasProducts.p₂ products {1} {1}

open example-signature-interpretation cat products terminal 1 unit conjunct

open import Data.List using (List; []; _∷_)
open import every using (Every; []; _∷_)
open import signature
import language-syntax
import label

open import example-signature

module L = language-syntax Sig

import indexed-family
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
  open ho-model.Matrix.interp Sig BaseInterp1

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0) , (label.b , 1) , (label.a , 1) , _

  open indexed-family._⇒f_
  open SemiLat._⇒_
  open join-semilattice._=>_
  open preorder._=>_

  -- Reproduce example-conjugate (fwd direction only, but via the matrix model instead)
  fwd-slice : _ → _
  fwd-slice n = ⟦ example.ex.query label.a ⟧tm .famf .transf (_ , input) .*→* .func .fun n

  -- Output depends on 1st label (would be ⊥ in the Galois example)
  test-1 : fwd-slice (· , (· , ⊤ , ·) , (· , ⊥ , ·) , (· , ⊥ , ·) , _) ≡ (⊤ , ·)
  test-1 = ≡-refl

  -- Output doesn't depend on 2nd label
  test-2 : fwd-slice (· , (· , ⊥ , ·) , (· , ⊤ , ·) , (· , ⊥ , ·) , _) ≡ (⊥ , ·)
  test-2 = ≡-refl

  -- Output depends on 3rd label (would be ⊥ in the Galois example)
  test-3 : fwd-slice (· , (· , ⊥ , ·) , (· , ⊥ , ·) , (· , ⊤ , ·) , _) ≡ (⊤ , ·)
  test-3 = ≡-refl
