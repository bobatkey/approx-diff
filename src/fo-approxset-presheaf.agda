{-# OPTIONS --postfix-projections --without-K #-}

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

-- For now this is how we state naturality (.commute).
infix 4 _≈_
_≈_ : ∀ {a b} {A : Set a} {B : Set b} → (A -> B) -> (A → B) -> Set (a ⊔ b)
f ≈ g = ∀ x → f x ≡ g x

-- But maybe too restrictive because then ⇒ₐ equations need to hold up to propositional equality..
postulate
  ∘ₐ-assoc : ∀ {W X Y Z} (f : Y ⇒ₐ Z) (g : X ⇒ₐ Y) (h : W ⇒ₐ X) → f ∘ₐ (g ∘ₐ h) ≡ (f ∘ₐ g) ∘ₐ h
  ∘ₐ-unitᵣ : ∀ {X Y} (f : X ⇒ₐ Y) → f ∘ₐ idₐ ≡ f
  ∘ₐ-unitₗ : ∀ {X Y} (f : X ⇒ₐ Y) → idₐ ∘ₐ f ≡ f

record _⇒_ {a b} (F : FOApproxSetPSh a) (G : FOApproxSetPSh b) : Set (suc (a ⊔ b)) where
  field
    at : ∀ (X : FOApproxSet) → F .obj X → G .obj X
    commute : ∀ {X Y : FOApproxSet} (f : X ⇒ₐ Y) → at X ∘ₛ F .map f ≈ G .map f ∘ₛ at Y

open _⇒_

-- Definitions for category
id : ∀ {a} {F : FOApproxSetPSh a} → F ⇒ F
id .at X = idₛ
id .commute f y = refl

_∘_ : ∀ {a} {F G H : FOApproxSetPSh a} → G ⇒ H → F ⇒ G → F ⇒ H
(ζ ∘ η) .at X = ζ .at X ∘ₛ η .at X
(ζ ∘ η) .commute {X}{Y} f y =
  trans (cong (ζ .at X) (η .commute f y)) (ζ .commute f (η .at Y y))

infixr 10 _∘_

-- Products
_⊗_ : ∀ {a b} → FOApproxSetPSh a → FOApproxSetPSh b → FOApproxSetPSh (a ⊔ b)
(F ⊗ G) .obj X = F .obj X × G .obj X
(F ⊗ G) .map f (x , y) .proj₁ = F .map f x
(F ⊗ G) .map f (x , y) .proj₂ = G .map f y

π₁ : ∀ {a} {F G : FOApproxSetPSh a} → (F ⊗ G) ⇒ F
π₁ .at X = proj₁
π₁ .commute f _ = refl

π₂ : ∀ {a} {F G : FOApproxSetPSh a} → (F ⊗ G) ⇒ G
π₂ .at X = proj₂
π₂ .commute f _ = refl

pair : ∀ {a} {F G H : FOApproxSetPSh a} → F ⇒ G → F ⇒ H → F ⇒ (G ⊗ H)
pair ζ η .at X x .proj₁ = ζ .at X x
pair ζ η .at X x .proj₂ = η .at X x
pair ζ η .commute f x = cong₂ _,_ (ζ .commute f x) (η .commute f x)

-- Sums
_+_ : ∀ {a} → FOApproxSetPSh a → FOApproxSetPSh a → FOApproxSetPSh a
(F + G) .obj X = F .obj X ⊎ G .obj X
(F + G) .map f (inj₁ x) = inj₁ (F .map f x)
(F + G) .map f (inj₂ x) = inj₂ (G .map f x)

inl : ∀ {a} {F G : FOApproxSetPSh a} → F ⇒ (F + G)
inl .at X = inj₁
inl .commute f _ = refl

inr : ∀ {a} {F G : FOApproxSetPSh a} → G ⇒ (F + G)
inr .at X = inj₂
inr .commute f _ = refl

[_,_] : ∀ {a} {E F G H : FOApproxSetPSh a} → (E ⊗ F) ⇒ H → (E ⊗ G) ⇒ H → (E ⊗ (F + G)) ⇒ H
[ ζ , η ] .at X (x , inj₁ y) = ζ .at X (x , y)
[ ζ , η ] .at X (x , inj₂ y) = η .at X (x , y)
[ ζ , η ] .commute f (x , inj₁ y) = ζ .commute f (x , y)
[ ζ , η ] .commute f (x , inj₂ y) = η .commute f (x , y)

-- Yoneda embedding
よ : FOApproxSet -> FOApproxSetPSh 0ℓ
よ Y .obj X = X ⇒ₐ Y
よ Y .map f g = g ∘ₐ f

-- Functions
_⊸_ : FOApproxSetPSh 0ℓ → FOApproxSetPSh 0ℓ → FOApproxSetPSh (suc 0ℓ)
(F ⊸ G) .obj X = (F ⊗ よ X) ⇒ G
(F ⊸ G) .map f η .at X (x , g) = η .at X (x , f ∘ₐ g)
(F ⊸ G) .map f η .commute {W} {Z} g (x , h) =
  begin
    η .at W (F .map g x , f ∘ₐ (h ∘ₐ g))
  ≡⟨ cong (λ f' → η .at W (F .map g x , f')) (∘ₐ-assoc f h g) ⟩
    η .at W (F .map g x , (f ∘ₐ h) ∘ₐ g)
  ≡⟨ η .commute g (x , f ∘ₐ h) ⟩
    G .map g (η .at Z (x , f ∘ₐ h))
  ∎
  where open ≡-Reasoning

eval : ∀ {F G : FOApproxSetPSh 0ℓ} → ((F ⊸ G) ⊗ F) ⇒ G
eval .at X (η , x) = η .at X (x , idₐ)
eval {F} {G} .commute {X} {Y} f (η , y) =
  begin
    η .at X (F .map f y , f ∘ₐ idₐ)
  ≡⟨ cong (λ f' → η .at X (F .map f y , f')) (trans (∘ₐ-unitᵣ f) (sym (∘ₐ-unitₗ f))) ⟩
    η .at X ((F ⊗ よ Y) .map f (y , idₐ))
  ≡⟨ η .commute f (y , idₐ) ⟩
    G .map f (η .at Y (y , idₐ))
  ∎
  where open ≡-Reasoning
