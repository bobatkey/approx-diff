{-# OPTIONS --postfix-projections --safe --without-K #-}

module fo-approxset-presheaf where

open import Level
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open import fo-approxset renaming (_⇒_ to _⇒ₐ_; _∘_ to _∘ₐ_)

-- Presheaf on FOApproxSet to Set
record FOApproxSetPSh : Set (suc 0ℓ) where
  field
    obj : FOApproxSet → Set
    map : ∀ {X Y : FOApproxSet} → (X ⇒ₐ Y) → obj Y → obj X
    -- preserves id, composition

open FOApproxSetPSh

infix 4 _≈_
_≈_ : ∀ {A B} → (A -> B) -> (A → B) -> Set
f ≈ g = ∀ x → f x ≡ g x

record _⇒_ (F G : FOApproxSetPSh) : Set (suc 0ℓ) where
  field
    func : ∀ (X : FOApproxSet) → F .obj X → G .obj X
    commute : ∀ {X Y : FOApproxSet} (f : X ⇒ₐ Y) → func X ∘ F .map f ≈ G .map f ∘ func Y
