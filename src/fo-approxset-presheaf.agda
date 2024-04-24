{-# OPTIONS --postfix-projections --safe --without-K #-}

module fo-approxset-presheaf where

open import Level
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function renaming (id to idₛ; _∘_ to _∘ₛ_)
open import Relation.Binary.PropositionalEquality
open import fo-approxset renaming (_⇒_ to _⇒ₐ_; id to idₐ; _∘_ to _∘ₐ_; _⊗_ to _⊗ₐ_)

-- Presheaf on FOApproxSet
record FOApproxSetPSh : Set (suc 0ℓ) where
  field
    obj : FOApproxSet → Set
    map : ∀ {X Y : FOApproxSet} → (X ⇒ₐ Y) → obj Y → obj X
    -- preserves id, composition

open FOApproxSetPSh

-- Come back to function equality, this for now
infix 4 _≈_
_≈_ : ∀ {A B} → (A -> B) -> (A → B) -> Set
f ≈ g = ∀ x → f x ≡ g x

record _⇒_ (F G : FOApproxSetPSh) : Set (suc 0ℓ) where
  field
    func : ∀ (X : FOApproxSet) → F .obj X → G .obj X
    commute : ∀ {X Y : FOApproxSet} (f : X ⇒ₐ Y) → func X ∘ₛ F .map f ≈ G .map f ∘ₛ func Y

open _⇒_

-- Definitions for category
id : ∀ {F} → F ⇒ F
id .func X = idₛ
id .commute f y = refl

_∘_ : ∀ {F G H} → G ⇒ H → F ⇒ G → F ⇒ H
(ζ ∘ η) .func X = ζ .func X ∘ₛ η .func X
(ζ ∘ η) .commute {X}{Y} f y =
  trans (cong (ζ .func X) (η .commute f y)) (ζ .commute f (η .func Y y))

infixr 10 _∘_

-- Products
module _ where
  _⊗_ : FOApproxSetPSh → FOApproxSetPSh → FOApproxSetPSh
  (F ⊗ G) .obj X = F .obj X × G .obj X
  (F ⊗ G) .map f (y₁ , y₂) = F .map f y₁ , G .map f y₂
