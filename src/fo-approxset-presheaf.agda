{-# OPTIONS --postfix-projections --safe --without-K #-}

module fo-approxset-presheaf where

open import Level
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function renaming (id to idₛ; _∘_ to _∘ₛ_)
open import Relation.Binary.PropositionalEquality
open import fo-approxset using (FOApproxSet) renaming (_⇒_ to _⇒ₐ_; id to idₐ; _∘_ to _∘ₐ_; _⊗_ to _⊗ₐ_)

-- Presheaf on FOApproxSet. Unsure about universe levels..
record FOApproxSetPSh a : Set (suc a) where
  field
    obj : FOApproxSet → Set a
    map : ∀ {X Y : FOApproxSet} → (X ⇒ₐ Y) → obj Y → obj X
    -- preserves id, composition

open FOApproxSetPSh

-- Come back to function equality, this for now
infix 4 _≈_
_≈_ : ∀ {a} {A B : Set a} → (A -> B) -> (A → B) -> Set a
f ≈ g = ∀ x → f x ≡ g x

record _⇒_ {a} (F G : FOApproxSetPSh a) : Set (suc a) where
  field
    func : ∀ (X : FOApproxSet) → F .obj X → G .obj X
    commute : ∀ {X Y : FOApproxSet} (f : X ⇒ₐ Y) → func X ∘ₛ F .map f ≈ G .map f ∘ₛ func Y

open _⇒_

-- Definitions for category
id : ∀ {a} {F : FOApproxSetPSh a} → F ⇒ F
id .func X = idₛ
id .commute f y = refl

_∘_ : ∀ {a} {F G H : FOApproxSetPSh a} → G ⇒ H → F ⇒ G → F ⇒ H
(ζ ∘ η) .func X = ζ .func X ∘ₛ η .func X
(ζ ∘ η) .commute {X}{Y} f y =
  trans (cong (ζ .func X) (η .commute f y)) (ζ .commute f (η .func Y y))

infixr 10 _∘_

-- Products
_⊗_ : ∀ {a} → FOApproxSetPSh a → FOApproxSetPSh a → FOApproxSetPSh a
(F ⊗ G) .obj X = F .obj X × G .obj X
(F ⊗ G) .map f (x , y) .proj₁ = F .map f x
(F ⊗ G) .map f (x , y) .proj₂ = G .map f y

π₁ : ∀ {a} {F G : FOApproxSetPSh a} → (F ⊗ G) ⇒ F
π₁ .func X = proj₁
π₁ .commute f _ = refl

π₂ : ∀ {a} {F G : FOApproxSetPSh a} → (F ⊗ G) ⇒ G
π₂ .func X = proj₂
π₂ .commute f _ = refl

pair : ∀ {a} {F G H : FOApproxSetPSh a} → F ⇒ G → F ⇒ H → F ⇒ (G ⊗ H)
pair ζ η .func X x .proj₁ = ζ .func X x
pair ζ η .func X x .proj₂ = η .func X x
pair ζ η .commute f x = cong₂ _,_ (ζ .commute f x) (η .commute f x)

-- Sums
_+_ : ∀ {a} → FOApproxSetPSh a → FOApproxSetPSh a → FOApproxSetPSh a
(F + G) .obj X = F .obj X ⊎ G .obj X
(F + G) .map f (inj₁ x) = inj₁ (F .map f x)
(F + G) .map f (inj₂ x) = inj₂ (G .map f x)

inl : ∀ {a} {F G : FOApproxSetPSh a} → F ⇒ (F + G)
inl .func X = inj₁
inl .commute f _ = refl

inr : ∀ {a} {F G : FOApproxSetPSh a} → G ⇒ (F + G)
inr .func X = inj₂
inr .commute f _ = refl

[_,_] : ∀ {a} {E F G H : FOApproxSetPSh a} → (E ⊗ F) ⇒ H → (E ⊗ G) ⇒ H → (E ⊗ (F + G)) ⇒ H
[ ζ , η ] .func X (x , inj₁ y) = ζ .func X (x , y)
[ ζ , η ] .func X (x , inj₂ y) = η .func X (x , y)
[ ζ , η ] .commute f (x , inj₁ y) = ζ .commute f (x , y)
[ ζ , η ] .commute f (x , inj₂ y) = η .commute f (x , y)

-- Functions
HomR : FOApproxSet -> FOApproxSetPSh 0ℓ
HomR Y .obj X = X ⇒ₐ Y
HomR Y .map f g = g ∘ₐ f

_⊸_ : FOApproxSetPSh 0ℓ → FOApproxSetPSh 0ℓ → FOApproxSetPSh (suc 0ℓ)
(F ⊸ G) .obj X = (F ⊗ HomR X) ⇒ G
(F ⊸ G) .map = {!   !}
