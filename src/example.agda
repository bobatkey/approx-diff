{-# OPTIONS --prop --postfix-projections --safe #-}

module example where

open import Level using (0ℓ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import prop
open import language-syntax
import nat
import label
import prop-setoid

------------------------------------------------------------------------------
-- Step 1: Make a language

data sort : Set where
  number label : sort

data op : List sort → sort → Set where
  zero : op [] number
  add  : op (number ∷ number ∷ []) number
  lbl  : label.label → op [] label

data rel : List sort → Set where
  equal-label : rel (label ∷ label ∷ [])

Sig : Signature 0ℓ
Sig .Signature.sort = sort
Sig .Signature.op = op
Sig .Signature.rel = rel

module L = language Sig

-- FIXME: example query. Given `List (label [×] nat)`, add up all the
-- elements labelled with a specific label:
--
--   sum [ snd e | e <- xs, equal-label 'a' (fst e) ]
--
--   sum (concatMap x (e. if equal-label 'a' (fst e) then return (snd e) else nil))
--
--   sum = fold zero (add (var zero) (var (succ zero)))

------------------------------------------------------------------------------
-- Step 2: Make a category for interpretation

import galois
import categories
open import grothendieck

module D = CategoryOfFamilies {os = 0ℓ} {es = 0ℓ} galois.cat
module DP = D.products galois.products

DB = categories.coproducts→booleans
       (D.terminal galois.terminal)
       (D.products.strongCoproducts galois.products)

open import language-interpretation D.cat
              (D.terminal galois.terminal)
              (DP.products)
              (DB)
              (D.lists galois.terminal galois.products)

module _ where

  open D.Mor
  open import fam
  open import categories
  open prop-setoid using (⊗-setoid; +-setoid; 𝟙)
    renaming (_⇒_ to _⇒s_)

  -- FIXME: use Strings for labels

  binary : ∀ X G → D.Mor (D.simple[ X , G ] DP.⊗ (D.simple[ X , G ] DP.⊗ D.simple[ prop-setoid.𝟙 {0ℓ} {0ℓ} , galois.𝟙 ])) D.simple[ prop-setoid.⊗-setoid X X , G galois.⊗ G ]
  binary X G .idxf .prop-setoid._⇒_.func (x , y , _) = x , y
  binary X G .idxf .prop-setoid._⇒_.func-resp-≈ (e₁ , e₂ , _) = e₁ , e₂
  binary X G .famf ._⇒f_.transf x = pair p₁ (p₁ ∘ p₂)
    where open HasProducts galois.products
          open Category galois.cat
  binary X G .famf ._⇒f_.natural (e₁ , e₂ , _) = {!!}
    where open HasProducts galois.products
          open Category galois.cat

--  halp :

  predicate : ∀ {X G} → (X ⇒s +-setoid (𝟙 {0ℓ} {0ℓ}) (𝟙 {0ℓ} {0ℓ})) →
              D.Mor D.simple[ X , G ]
                    (DB .HasBooleans.Bool)
  predicate f .idxf = f
  predicate f .famf ._⇒f_.transf x = {!!}
  predicate f .famf ._⇒f_.natural = {!!}


  BaseInterp : SignatureInterp Sig
  BaseInterp .SignatureInterp.⟦sort⟧ number = D.simple[ nat.ℕₛ , galois.Presence ]
  BaseInterp .SignatureInterp.⟦sort⟧ label = D.simple[ label.Label , galois.Presence ]
  BaseInterp .SignatureInterp.⟦op⟧ zero = D.simplef[ nat.zero-m , galois.present ]
  BaseInterp .SignatureInterp.⟦op⟧ add = D.Mor-∘ D.simplef[ nat.add , galois.combinePresence ] (binary _ _)
  BaseInterp .SignatureInterp.⟦op⟧ (lbl l) = D.simplef[ prop-setoid.const label.Label l , galois.present ]
  BaseInterp .SignatureInterp.⟦rel⟧ equal-label = D.Mor-∘ (predicate label.equal-label) (binary label.Label galois.Presence)

open interp Sig BaseInterp

interp : ∀ {Γ τ} → Γ L.⊢ τ → D.Mor ⟦ Γ ⟧ctxt ⟦ τ ⟧ty
interp = ⟦_⟧tm
