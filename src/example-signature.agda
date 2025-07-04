{-# OPTIONS --postfix-projections --prop --safe #-}

module example-signature where

open import Level using (0ℓ)
open import signature using (Signature)
open import Data.List using (List; []; _∷_)
import label

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
