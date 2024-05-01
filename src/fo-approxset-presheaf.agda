{-# OPTIONS --postfix-projections --without-K #-}

module fo-approxset-presheaf where

open import Level
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function renaming (id to idₛ; _∘_ to _∘ₛ_)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (cong; _≡_) renaming (refl to ≡-refl; trans to ≡-trans)
open IsEquivalence
open Setoid using (Carrier; _≈_; isEquivalence)
open import fo-approxset
  using (FOApproxSet)
  renaming (
    _⇒_ to _⇒ₐ_; _≃m_ to _≃mₐ_; ≃m-setoid to ≃mₐ-setoid; id to idₐ; _∘_ to _∘ₐ_; _⊗_ to _⊗ₐ_;
    ∘-resp-≃m to ∘ₐ-resp-≃mₐ; ∘-assoc to ∘ₐ-assoc; ∘-unitₗ to ∘ₐ-unitₗ; ∘-unitᵣ to ∘ₐ-unitᵣ
  )

-- Presheaf on FOApproxSet.
record FOApproxSetPSh a : Set (suc a) where
  field
    obj : FOApproxSet → Setoid a a
    map : ∀ {X Y} → (X ⇒ₐ Y) → obj Y .Carrier → obj X .Carrier
    -- Cartesian closure requires generalising to f ≃mₐ f'
    map-resp-≈ : ∀ {X Y} {f f' : X ⇒ₐ Y} → f ≃mₐ f' → ∀ {x y} → obj Y ._≈_ x y → obj X ._≈_ (map f x) (map f' y)
    preserves-∘ : ∀ {X Y Z} (f : Y ⇒ₐ Z) (g : X ⇒ₐ Y) → ∀ x → obj X ._≈_ (map g (map f x)) (map (f ∘ₐ g) x)
    preserves-id : ∀ {X Y} (f : X ⇒ₐ Y) → ∀ x → obj X ._≈_ (idₛ (map f x)) (map f (idₛ x))

open FOApproxSetPSh

record _⇒_ {a b} (F : FOApproxSetPSh a) (G : FOApproxSetPSh b) : Set (suc (a ⊔ b)) where
  field
    at : ∀ X → F .obj X .Carrier → G .obj X .Carrier
    at-resp-≈ : ∀ X {x y} → F .obj X ._≈_ x y → G .obj X ._≈_ (at X x) (at X y)
    commute : ∀ {X Y} (f : X ⇒ₐ Y) → ∀ x → G .obj X ._≈_ (at X (F .map f x)) (G .map f (at Y x))

open _⇒_

record _≃m_ {a b} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} (η ζ : F ⇒ G) : Set (suc (a ⊔ b)) where
  field
    -- Cartesian closure requires generalising to x ≃ x'
    eqat : ∀ X {x x'} → F .obj X ._≈_ x x' → G .obj X ._≈_ (η .at X x) (ζ .at X x')

open _≃m_

module _ where
  ≃m-setoid : ∀ {a b} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} → Setoid (suc (a ⊔ b)) (suc (a ⊔ b))
  ≃m-setoid {F = F} {G} .Carrier = F ⇒ G
  ≃m-setoid ._≈_ η ζ = η ≃m ζ
  ≃m-setoid {G = G} .isEquivalence .refl {η} .eqat X x = η .at-resp-≈ X x
  ≃m-setoid {F = F} {G} .isEquivalence .sym η≃ζ .eqat X x =
    G .obj X .isEquivalence .sym (η≃ζ .eqat X (F .obj X .isEquivalence .sym x))
  ≃m-setoid {F = F} {G} .isEquivalence .trans η≃ζ η≃ε .eqat X x =
    G .obj X .isEquivalence .trans (η≃ζ .eqat X x) (η≃ε .eqat X (F .obj X .isEquivalence .refl))

-- Some setoid helpers that are probably in stdlib somewhere
≡-to-≈ : ∀ {a b} (X : Setoid a b) {x y : X .Carrier} → x ≡ y → X ._≈_ x y
≡-to-≈ X {x} {.x} ≡-refl = X .isEquivalence .refl

⊗-setoid : ∀ {a b} (X : Setoid a a) (Y : Setoid b b) → Setoid (a ⊔ b) (a ⊔ b)
⊗-setoid X Y .Carrier = X .Carrier × Y .Carrier
⊗-setoid X Y ._≈_ (x₁ , y₁) (x₂ , y₂) = X ._≈_ x₁ x₂ × Y ._≈_ y₁ y₂
⊗-setoid X Y .isEquivalence .refl .proj₁ = X .isEquivalence .refl
⊗-setoid X Y .isEquivalence .refl .proj₂ = Y .isEquivalence .refl
⊗-setoid X Y .isEquivalence .sym (x₁≈y₁ , _) .proj₁ = X .isEquivalence .sym x₁≈y₁
⊗-setoid X Y .isEquivalence .sym (_ , x₂≈y₂) .proj₂ = Y .isEquivalence .sym x₂≈y₂
⊗-setoid X Y .isEquivalence .trans (x₁≈y₁ , _) (y₁≈z₁ , _) .proj₁ = X .isEquivalence .trans x₁≈y₁ y₁≈z₁
⊗-setoid X Y .isEquivalence .trans (_ , x₂≈y₂) (_ , y₂≈z₂) .proj₂ = Y .isEquivalence .trans x₂≈y₂ y₂≈z₂

+-setoid : ∀ {a} (X : Setoid a a) (Y : Setoid a a) → Setoid a a
+-setoid X Y .Carrier = X .Carrier ⊎ Y .Carrier
+-setoid X Y ._≈_ (inj₁ x) (inj₁ y) = X ._≈_ x y
+-setoid X Y ._≈_ (inj₂ x) (inj₂ y) = Y ._≈_ x y
+-setoid X Y ._≈_ (inj₁ x) (inj₂ y) = Lift _ 𝟘
+-setoid X Y ._≈_ (inj₂ x) (inj₁ y) = Lift _ 𝟘
+-setoid X Y .isEquivalence .refl {inj₁ x} = X .isEquivalence .refl
+-setoid X Y .isEquivalence .refl {inj₂ x} = Y .isEquivalence .refl
+-setoid X Y .isEquivalence .sym {inj₁ x} {inj₁ y} = X .isEquivalence .sym
+-setoid X Y .isEquivalence .sym {inj₂ x} {inj₂ y} = Y .isEquivalence .sym
+-setoid X Y .isEquivalence .trans {inj₁ x} {inj₁ y} {inj₁ z} = X .isEquivalence .trans
+-setoid X Y .isEquivalence .trans {inj₂ x} {inj₂ y} {inj₂ z} = Y .isEquivalence .trans

-- Definitions for category
id : ∀ {a} {F : FOApproxSetPSh a} → F ⇒ F
id .at X = idₛ
id .at-resp-≈ X = idₛ
id {F = F} .commute = F .preserves-id

_∘_ : ∀ {a} {F G H : FOApproxSetPSh a} → G ⇒ H → F ⇒ G → F ⇒ H
(ζ ∘ η) .at X = ζ .at X ∘ₛ η .at X
(ζ ∘ η) .at-resp-≈ X = ζ .at-resp-≈ X ∘ₛ η .at-resp-≈ X
_∘_ {H = H} ζ η .commute {X}{Y} f y =
  H .obj X .isEquivalence .trans (ζ .at-resp-≈ X (η .commute f y)) (ζ .commute f (η .at Y y))

infixr 10 _∘_

-- Products
_⊗_ : ∀ {a b} → FOApproxSetPSh a → FOApproxSetPSh b → FOApproxSetPSh (a ⊔ b)
(F ⊗ G) .obj X = ⊗-setoid (F .obj X) (G .obj X)
(F ⊗ G) .map f (x , y) .proj₁ = F .map f x
(F ⊗ G) .map f (x , y) .proj₂ = G .map f y
(F ⊗ G) .map-resp-≈ f (x , y) .proj₁ = F .map-resp-≈ f x
(F ⊗ G) .map-resp-≈ f (x , y) .proj₂ = G .map-resp-≈ f y
(F ⊗ G) .preserves-∘ f g (x , y) .proj₁ = F .preserves-∘ f g x
(F ⊗ G) .preserves-∘ f g (x , y) .proj₂ = G .preserves-∘ f g y
(F ⊗ G) .preserves-id f (x , y) .proj₁ = F .preserves-id f x
(F ⊗ G) .preserves-id f (x , y) .proj₂ = G .preserves-id f y

π₁ : ∀ {a b} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} → (F ⊗ G) ⇒ F
π₁ .at X = proj₁
π₁ .at-resp-≈ X = proj₁
π₁ {F = F} .commute {X} f _ = F .obj X .isEquivalence .refl

π₂ : ∀ {a b} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} → (F ⊗ G) ⇒ G
π₂ .at X = proj₂
π₂ .at-resp-≈ X = proj₂
π₂ {G = G} .commute {X} f _ = G .obj X .isEquivalence .refl

pair : ∀ {a b c} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} {H : FOApproxSetPSh c} → F ⇒ G → F ⇒ H → F ⇒ (G ⊗ H)
pair ζ η .at X x .proj₁ = ζ .at X x
pair ζ η .at X x .proj₂ = η .at X x
pair ζ η .at-resp-≈ X x .proj₁ = ζ .at-resp-≈ X x
pair ζ η .at-resp-≈ X x .proj₂ = η .at-resp-≈ X x
pair ζ η .commute f x .proj₁ = ζ .commute f x
pair ζ η .commute f x .proj₂ = η .commute f x

-- Sums
_+_ : ∀ {a} → FOApproxSetPSh a → FOApproxSetPSh a → FOApproxSetPSh a
(F + G) .obj X = +-setoid (F .obj X) (G .obj X)
(F + G) .map f (inj₁ x) = inj₁ (F .map f x)
(F + G) .map f (inj₂ x) = inj₂ (G .map f x)
(F + G) .map-resp-≈ f {inj₁ x} {inj₁ y} = F .map-resp-≈ f
(F + G) .map-resp-≈ f {inj₂ x} {inj₂ y} = G .map-resp-≈ f
(F + G) .preserves-∘ f g (inj₁ x) = F .preserves-∘ f g x
(F + G) .preserves-∘ f g (inj₂ x) = G .preserves-∘ f g x
(F + G) .preserves-id f (inj₁ x) = F .preserves-id f x
(F + G) .preserves-id f (inj₂ x) = G .preserves-id f x

inl : ∀ {a} {F G : FOApproxSetPSh a} → F ⇒ (F + G)
inl .at X = inj₁
inl .at-resp-≈ X = idₛ
inl {F = F} .commute {X} f _ = F .obj X .isEquivalence .refl

inr : ∀ {a} {F G : FOApproxSetPSh a} → G ⇒ (F + G)
inr .at X = inj₂
inr .at-resp-≈ X = idₛ
inr {G = G} .commute {X} f _ = G .obj X .isEquivalence .refl

[_,_] : ∀ {a} {E F G H : FOApproxSetPSh a} → (E ⊗ F) ⇒ H → (E ⊗ G) ⇒ H → (E ⊗ (F + G)) ⇒ H
[ ζ , η ] .at X (x , inj₁ y) = ζ .at X (x , y)
[ ζ , η ] .at X (x , inj₂ y) = η .at X (x , y)
[ ζ , η ] .at-resp-≈ X {x₁ , inj₁ y₁} {x₂ , inj₁ y₂} = ζ .at-resp-≈ X
[ ζ , η ] .at-resp-≈ X {x₁ , inj₂ y₁} {x₂ , inj₂ y₂} = η .at-resp-≈ X
[ ζ , η ] .commute f (x , inj₁ y) = ζ .commute f (x , y)
[ ζ , η ] .commute f (x , inj₂ y) = η .commute f (x , y)

-- Yoneda embedding Y ↦ Hom(-, Y)
よ : FOApproxSet -> FOApproxSetPSh 0ℓ
よ Y .obj X = ≃mₐ-setoid X Y
よ Y .map f g = g ∘ₐ f
よ Y .map-resp-≈ {X} {Z} f≈f' g≈ = ∘ₐ-resp-≃mₐ g≈ f≈f'
よ Y .preserves-∘ {X} {Z} f g h = ≃mₐ-setoid X Y .isEquivalence .sym (∘ₐ-assoc h f g)
よ Y .preserves-id {X} {Z} f g =
  ≃mₐ-setoid X Y .isEquivalence .trans
    (≡-to-≈ (≃mₐ-setoid X Y) ≡-refl) (≡-to-≈ (≃mₐ-setoid X Y) (cong (λ g' → g' ∘ₐ f) {_} {g} ≡-refl))

-- Functions. (F ⊗ よ X) ⇒ G and よ X ⇒ (F ⊸ G) are isomorphic
_⊸_ : ∀ {a b} → FOApproxSetPSh a → FOApproxSetPSh b → FOApproxSetPSh (suc (a ⊔ b))
(F ⊸ G) .obj X = ≃m-setoid {F = F ⊗ よ X} {G}
(F ⊸ G) .map f η .at X (x , g) = η .at X (x , f ∘ₐ g)
(F ⊸ G) .map f η .at-resp-≈ X (x , g) =
  η .at-resp-≈ X (x , ∘ₐ-resp-≃mₐ {f = f} (≃mₐ-setoid _ _ .isEquivalence .refl) g)
(F ⊸ G) .map f η .commute {Y} {Z} g (x , h) =
  G .obj Y .isEquivalence .trans
    (η .at-resp-≈ Y (F .obj Y .isEquivalence .refl , ∘ₐ-assoc f h g)) (η .commute g (x , f ∘ₐ h))
(F ⊸ G) .map-resp-≈ f η .eqat X (x , g) = η .eqat X (x , ∘ₐ-resp-≃mₐ f g)
(F ⊸ G) .preserves-∘ f g η .eqat X (x , h) = η .at-resp-≈ X (x , {!   !}) -- ∘ₐ-assoc f g h
(F ⊸ G) .preserves-id f η .eqat X (x , h) = {!   !} --≡-to-≈ (G .obj X) ≡-refl

eval : ∀ {a b} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} → ((F ⊸ G) ⊗ F) ⇒ G
eval .at X (η , x) = η .at X (x , idₐ)
eval .at-resp-≈ X (η , x) = η .eqat X (x , ≃mₐ-setoid X _ .isEquivalence .refl)
eval {F = F} {G} .commute {X} {Y} f (η , y) =
  G .obj X .isEquivalence .trans
    (η .at-resp-≈ X (F .obj X .isEquivalence .refl ,
     ≃mₐ-setoid X Y .isEquivalence .trans (∘ₐ-unitᵣ f) (≃mₐ-setoid X Y .isEquivalence .sym (∘ₐ-unitₗ f))))
    (η .commute f (y , idₐ))

lambda : ∀ {a b c} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} {H : FOApproxSetPSh c} → (F ⊗ G) ⇒ H → F ⇒ (G ⊸ H)
lambda {F = F} η .at X x .at Y (y , f) = η .at Y (F .map f x , y)
lambda {F = F} η .at X x .at-resp-≈ Y (y , f) =
  η .at-resp-≈ Y (F .map-resp-≈ f (F .obj X .isEquivalence .refl) , y)
lambda {F = F} {G} {H} η .at X x .commute {Y} {Z} f (z , g) =
  H .obj Y .isEquivalence .trans
    (η .at-resp-≈ Y (F .obj Y .isEquivalence .sym (F .preserves-∘ g f x) , G .obj Y .isEquivalence .refl))
    (η .commute f (F .map g x , z))
lambda {F = F} {G} η .at-resp-≈ X x .eqat Y (y , f) = η .at-resp-≈ Y (F .map-resp-≈ f x , y)
lambda {F = F} {G} η .commute f x .eqat Z (z , g) = η .at-resp-≈ Z ({!   !} , z) -- F .preserves-∘ f g x
