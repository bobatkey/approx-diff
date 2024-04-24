{-# OPTIONS --postfix-projections --safe --without-K #-}

module fo-approxset-presheaf where

open import Level
open import Function renaming (id to idₛ; _∘_ to _∘ₛ_)
open import Relation.Binary.PropositionalEquality
open import fo-approxset renaming (_⇒_ to _⇒ₐ_; id to idₐ; _∘_ to _∘ₐ_)

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

≈-sym : ∀ {A B} {f : A → B} {g : A → B} -> f ≈ g -> g ≈ f
≈-sym f≈g x = sym (f≈g x)

∘-cong₁ : ∀ {A B C} (f g : B → C) (h : A → B) -> f ≈ g → f ∘ₛ h ≈ g ∘ₛ h
∘-cong₁ f g h f≈g x = f≈g (h x)

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
_∘_ {F}{G}{H} ζ η .commute {X}{Y} f y =
  let q : H .map f ∘ₛ ζ .func Y ∘ₛ η .func Y ≈ ζ .func X ∘ₛ G .map f ∘ₛ η .func Y
      q = λ x → ≈-sym (ζ .commute f) (η .func Y x) in
  let q' : ζ .func X ∘ₛ G .map f ∘ₛ η .func Y ≈ ζ .func X ∘ₛ η .func X ∘ₛ F .map f
      q' = λ x → cong (ζ .func X) (≈-sym (η .commute f) x) in
  trans (sym (q' y)) (sym (q y))
