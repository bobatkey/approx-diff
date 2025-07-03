{-# OPTIONS --prop --postfix-projections --safe #-}

module every where

open import Level using (_⊔_)
open import Data.List using (List; []; _∷_)

data Every {ℓ₁ ℓ₂} {A : Set ℓ₁} (P : A → Set ℓ₂) : List A → Set (ℓ₁ ⊔ ℓ₂) where
  []  : Every P []
  _∷_ : ∀ {x xs} → P x → Every P xs → Every P (x ∷ xs)
