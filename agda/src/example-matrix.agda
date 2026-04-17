{-# OPTIONS --prop --postfix-projections --safe #-}

module example-matrix where

open import Level using (0ℓ)
open import categories using (Category)

import join-semilattice-category as JSL
import galois

-- TWO (= 𝟚) as an object of SemiLat, extracted from galois.TWO.
TWO : JSL.Obj
TWO .JSL.Obj.carrier = galois.TWO .galois.Obj.carrier
TWO .JSL.Obj.joins = galois.TWO .galois.Obj.joins
