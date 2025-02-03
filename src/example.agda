{-# OPTIONS --prop --postfix-projections --safe #-}

module example where

open import Level using (0ℓ)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (inj₁; inj₂)
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

-- example query. Given `List (label [×] nat)`, add up all the
-- elements labelled with a specific label:
--
--   sum [ snd e | e <- xs, equal-label 'a' (fst e) ]
--
--   sum (concatMap x (e. if equal-label 'a' (fst e) then return (snd e) else nil))
--
--   sum = fold zero (add (var zero) (var (succ zero)))

module ex where
  open L

  sum : ∀ {Γ} → Γ ⊢ list (base number) → Γ ⊢ base number
  sum = fold (bop zero []) (bop add (var zero ∷ var (succ zero) ∷ []))

  `_ : ∀ {Γ} → label.label → Γ ⊢ base label
  ` l = bop (lbl l) []

  _≟_ : ∀ {Γ} → Γ ⊢ base label → Γ ⊢ base label → Γ ⊢ bool
  M ≟ N = brel equal-label (M ∷ N ∷ [])

  query : label.label → emp , list (base label [×] base number) ⊢ base number
  query l = sum (from var zero collect
                 when fst (var zero) ≟ (` l) ；
                 return (snd (var zero)))

------------------------------------------------------------------------------
-- Step 2: Make a category for interpretation

import galois
import categories
import grothendieck

module D = grothendieck.CategoryOfFamilies 0ℓ galois.cat
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
  open import Data.Product using (_,_)
  open import prop
  open prop-setoid using (⊗-setoid; +-setoid; 𝟙; module ≈-Reasoning)
    renaming (_⇒_ to _⇒s_)

  -- FIXME: use Strings for labels

  binary : ∀ {X G} →
            D.Mor (D.simple[ X , G ] DP.⊗ (D.simple[ X , G ] DP.⊗ D.simple[ 𝟙 {0ℓ} {0ℓ} , galois.𝟙 ]))
                  D.simple[ ⊗-setoid X X , G galois.⊗ G ]
  binary = D.Mor-∘ DP.simple-monoidal (pair p₁ (D.Mor-∘ p₁ p₂))
    where open HasProducts DP.products

  module _ where
    open galois hiding (𝟙)
    open prop-setoid using (IsEquivalence)
    open IsEquivalence

    halp : ∀ {G} x → G ⇒g DB .HasBooleans.Bool .D.Obj.fam .Fam.fm x
    halp (inj₁ _) = to-𝟙 _
    halp (inj₂ _) = to-𝟙 _

    halp-natural : ∀ {G x₁ x₂}
                   (e : +-setoid (𝟙 {0ℓ} {0ℓ}) (𝟙 {0ℓ} {0ℓ}) .prop-setoid.Setoid._≈_ x₁ x₂) →
                   halp {G} x₂ ≃g (DB .HasBooleans.Bool .D.Obj.fam .Fam.subst {x₁} {x₂} e ∘g halp {G} x₁)
    halp-natural {G} {inj₁ x} {inj₁ x₁} e = galois.terminal .HasTerminal.terminal-unique _ _ _
    halp-natural {G} {inj₂ y} {inj₂ y₁} e = galois.terminal .HasTerminal.terminal-unique _ _ _

    predicate : ∀ {X G} → (X ⇒s +-setoid (𝟙 {0ℓ} {0ℓ}) (𝟙 {0ℓ} {0ℓ})) →
                D.Mor D.simple[ X , G ] (DB .HasBooleans.Bool)
    predicate f .idxf = f
    predicate f .famf ._⇒f_.transf x = halp (f ._⇒s_.func x)
    predicate f .famf ._⇒f_.natural {x₁} {x₂} e =
      ≃g-isEquivalence .trans (cat .Category.id-right)
                              (halp-natural {x₁ = f ._⇒s_.func x₁} {x₂ = f ._⇒s_.func x₂} (f ._⇒s_.func-resp-≈ e))

  BaseInterp : SignatureInterp Sig
  BaseInterp .SignatureInterp.⟦sort⟧ number = D.simple[ nat.ℕₛ , galois.Presence ]
  BaseInterp .SignatureInterp.⟦sort⟧ label = D.simple[ label.Label , galois.Presence ]
  BaseInterp .SignatureInterp.⟦op⟧ zero = D.simplef[ nat.zero-m , galois.present ]
  BaseInterp .SignatureInterp.⟦op⟧ add = D.Mor-∘ D.simplef[ nat.add , galois.combinePresence ] binary
  BaseInterp .SignatureInterp.⟦op⟧ (lbl l) = D.simplef[ prop-setoid.const label.Label l , galois.present ]
  BaseInterp .SignatureInterp.⟦rel⟧ equal-label = D.Mor-∘ (predicate label.equal-label) binary

open interp Sig BaseInterp

open galois
open import fam
open _⇒f_
open D.Mor
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Unit using (tt)
open import join-semilattice

input : List (label.label × nat.ℕ)
input = (label.a , nat.zero) ∷
        (label.b , nat.succ nat.zero) ∷
        (label.a , nat.succ nat.zero) ∷
        []

back-slice : label.label → _
back-slice l = ⟦ ex.query l ⟧tm .famf .transf (_ , input) ._⇒g_.bwd  ._=>_.func pr .proj₂

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Querying for the 'a' label uses the 1st and 3rd numbers
test1 : back-slice label.a ≡ ((ab , pr) , (ab , ab) , (ab , pr) , tt)
test1 = refl

-- Querying for the 'b' label uses the 2nd number
test2 : back-slice label.b ≡ ((ab , ab) , (ab , pr) , (ab , ab) , tt)
test2 = refl
