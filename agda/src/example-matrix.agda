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
  module Mat = Category cat

import example-signature-interpretation
unit : Mat._⇒_ 0 2
unit = HasInitial.from-initial initial {2}

conjunct : Mat._⇒_ (HasProducts.prod products 2 2) 2
conjunct = HasProducts.p₁ products {2} {2} +m HasProducts.p₂ products {2} {2}

open example-signature-interpretation cat products terminal 2 unit conjunct
