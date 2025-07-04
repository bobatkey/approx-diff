{-# OPTIONS --prop --postfix-projections #-}

module example where

open import Level using (0ℓ; lift)
open import Data.List using (List; []; _∷_)
open import every using (Every; []; _∷_)
open import signature
import fam
import join-semilattice-category
import join-semilattice
import preorder
import language-syntax
import nat
import label
import prop-setoid

open import example-signature

module L = language-syntax Sig

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

  sum : ∀ {Γ} → Γ ⊢ list (base number) [→] base number
  sum = lam (fold (bop zero []) (bop add (var zero ∷ var (succ zero) ∷ [])) (var zero))

  `_ : ∀ {Γ} → label.label → Γ ⊢ base label
  ` l = bop (lbl l) []

  _≟_ : ∀ {Γ} → Γ ⊢ base label → Γ ⊢ base label → Γ ⊢ bool
  M ≟ N = brel equal-label (M ∷ N ∷ [])

  query : label.label → emp , list (base label [×] base number) ⊢ base number
  query l = app sum
                (from var zero collect
                 when fst (var zero) ≟ (` l) ；
                 return (snd (var zero)))



open import two using (I; O)
open import Data.Unit using (tt)
open import Data.Product using (_,_; _×_; proj₁; proj₂)

open import ho-model
open import example-signature-interpretation
open interp Sig BaseInterp

open fam._⇒f_
open prop-setoid._⇒_
open prop-setoid.Setoid
open join-semilattice-category._⇒_
open join-semilattice._=>_
open preorder._=>_

open L hiding (_,_)

input2 : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
input2 = 3 , (label.a , 56) , (label.b , 90) , (label.a , 1) , _

back-slice : label.label → _
back-slice l = ⟦ ex.query l ⟧tm .famf .transf (_ , input2) .proj₂ .*→* .func .fun I .proj₂

open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

_ = {!⟦ ex.query label.a ⟧tm .idxf .func (_ , input2)!}

-- Querying for the 'a' label uses the 1st and 3rd numbers
test1 : back-slice label.a ≡ ((O , I) , (O , O) , (O , I) , _)
test1 = ≡-refl

-- Querying for the 'b' label uses the 2nd number
test2 : back-slice label.b ≡ ((O , O) , (O , I) , (O , O) , _)
test2 = ≡-refl
