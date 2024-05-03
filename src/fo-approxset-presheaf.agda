{-# OPTIONS --postfix-projections --without-K #-}

module fo-approxset-presheaf where

open import Level
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function renaming (id to idₛ; _∘_ to _∘ₛ_)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; _≡_; setoid) renaming (refl to ≡-refl; trans to ≡-trans)
open IsEquivalence
open Setoid using (Carrier; _≈_; isEquivalence)
open import basics
open import fo-approxset
    using (FOApproxSet; ℒ-map; ℒ-map-resp-≃; ℒ-map-preserves-id; ℒ-map-preserves-∘; ℒ-unit-commute)
    renaming (
      _⇒_ to _⇒ₐ_; _≃m_ to _≃mₐ_; ≃m-setoid to ≃mₐ-setoid; id to idₐ; _∘_ to _∘ₐ_; _⊗_ to _⊗ₐ_;
      ∘-resp-≃m to ∘ₐ-resp-≃mₐ; ∘-assoc to ∘ₐ-assoc; ∘-unitₗ to ∘ₐ-unitₗ; ∘-unitᵣ to ∘ₐ-unitᵣ;
      ℒ to ℒₐ; ℒ-unit to ℒₐ-unit; ℒ-join to ℒₐ-join
    )

-- Presheaf on FOApproxSet.
record FOApproxSetPSh a : Set (suc a) where
  field
    obj : FOApproxSet → Setoid a a
    map : ∀ {X Y} → (X ⇒ₐ Y) → obj Y .Carrier → obj X .Carrier
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
    eqat : ∀ X {x x'} → F .obj X ._≈_ x x' → G .obj X ._≈_ (η .at X x) (ζ .at X x')

open _≃m_

module _ where
  ≃m-setoid : ∀ {a b} (F : FOApproxSetPSh a) (G : FOApproxSetPSh b) → Setoid (suc (a ⊔ b)) (suc (a ⊔ b))
  ≃m-setoid F G .Carrier = F ⇒ G
  ≃m-setoid F G ._≈_ η ζ = η ≃m ζ
  ≃m-setoid F G .isEquivalence .refl {η} .eqat X x = η .at-resp-≈ X x
  ≃m-setoid F G .isEquivalence .sym η≃ζ .eqat X x =
    G .obj X .isEquivalence .sym (η≃ζ .eqat X (F .obj X .isEquivalence .sym x))
  ≃m-setoid F G .isEquivalence .trans η≃ζ ζ≃ε .eqat X x =
    G .obj X .isEquivalence .trans (η≃ζ .eqat X x) (ζ≃ε .eqat X (F .obj X .isEquivalence .refl))

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

-- Terminal object
module _ where
  open import Data.Unit.Properties renaming (≡-setoid to 𝟙) public

  ⊤ : FOApproxSetPSh 0ℓ
  ⊤ .obj X = 𝟙
  ⊤ .map f _ = tt
  ⊤ .map-resp-≈ f _ = 𝟙 .isEquivalence .refl
  ⊤ .preserves-∘ f g _ = 𝟙 .isEquivalence .refl
  ⊤ .preserves-id f _ = 𝟙 .isEquivalence .refl

  terminal : ∀ {a} {F : FOApproxSetPSh a} → F ⇒ ⊤
  terminal .at X _ = tt
  terminal .at-resp-≈ X _ = 𝟙 .isEquivalence .refl
  terminal .commute f x = 𝟙 .isEquivalence .refl

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
よ Y .map-resp-≈ f g = ∘ₐ-resp-≃mₐ g f
よ Y .preserves-∘ {X} f g h = ≃mₐ-setoid X Y .isEquivalence .sym (∘ₐ-assoc h f g)
よ Y .preserves-id {X} f g =
  ≃mₐ-setoid X Y .isEquivalence .trans
    (≡-to-≈ (≃mₐ-setoid X Y) ≡-refl) (≡-to-≈ (≃mₐ-setoid X Y) (cong (λ g' → g' ∘ₐ f) {_} {g} ≡-refl))

-- Functions. (F ⊗ よ X) ⇒ G and よ X ⇒ (F ⊸ G) are isomorphic
_⊸_ : ∀ {a b} → FOApproxSetPSh a → FOApproxSetPSh b → FOApproxSetPSh (suc (a ⊔ b))
(F ⊸ G) .obj X = ≃m-setoid (F ⊗ よ X) G
(F ⊸ G) .map f η .at X (x , g) = η .at X (x , f ∘ₐ g)
(F ⊸ G) .map f η .at-resp-≈ X (x , g) =
  η .at-resp-≈ X (x , ∘ₐ-resp-≃mₐ {f = f} (≃mₐ-setoid _ _ .isEquivalence .refl) g)
(F ⊸ G) .map f η .commute {Y} {Z} g (x , h) =
  G .obj Y .isEquivalence .trans
    (η .at-resp-≈ Y (F .obj Y .isEquivalence .refl , ∘ₐ-assoc f h g)) (η .commute g (x , f ∘ₐ h))
(F ⊸ G) .map-resp-≈ f η .eqat X (x , g) = η .eqat X (x , ∘ₐ-resp-≃mₐ f g)
(F ⊸ G) .preserves-∘ {Y} {Z = Z} f g η .eqat X {_ , h₁} (x , h) =
  η .at-resp-≈ X (
    x ,
    ≃mₐ-setoid X Z .isEquivalence .trans
      (∘ₐ-assoc f g h₁) (∘ₐ-resp-≃mₐ {f = f ∘ₐ g} (≃mₐ-setoid Y Z .isEquivalence .refl) h)
  )
(F ⊸ G) .preserves-id {Y} {Z} f η .eqat X (x , h) =
  η .at-resp-≈ X (x , ∘ₐ-resp-≃mₐ {f = f} (≃mₐ-setoid Y Z .isEquivalence .refl) h)

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
lambda {F = F} {G} η .commute {X} {Y} f x .eqat Z (z , g) =
  η .at-resp-≈ Z (
    F .obj Z .isEquivalence .trans
      (F .preserves-∘ f _ x)
      (F .map-resp-≈ (∘ₐ-resp-≃mₐ {f = f} (≃mₐ-setoid X Y .isEquivalence .refl) g) (F .obj Y .isEquivalence .refl)) ,
    z
  )

-- prove law relating eval and lambda

-- Any old set becomes a constant presheaf
Disc : Set → FOApproxSetPSh 0ℓ
Disc A .obj X = setoid A
Disc A .map f = idₛ
Disc A .map-resp-≈ f = idₛ
Disc A .preserves-∘ f g x = ≡-refl
Disc A .preserves-id f x = ≡-refl

Disc-f : ∀ {A B} → (A → B) → Disc A ⇒ Disc B
Disc-f f .at X = f
Disc-f f .at-resp-≈ X = cong f
Disc-f f .commute g x = ≡-refl

Disc-const : ∀ {A} → A → ⊤ ⇒ Disc A
Disc-const x .at X _ = x
Disc-const x .at-resp-≈ X _ = ≡-refl
Disc-const x .commute f _ = ≡-refl

Disc-reflects-products : ∀ {A B} → (Disc A ⊗ Disc B) ⇒ Disc (A × B)
Disc-reflects-products .at X = idₛ
Disc-reflects-products .at-resp-≈ X (x , y) = cong₂ _,_ x y
Disc-reflects-products .commute f (x , y) = ≡-refl

-- Helper for binary predicate over a set
module _ where
  open import Relation.Binary using (Decidable; Rel)
  open import Relation.Nullary

  binPred : ∀ {ℓ A} {_∼_ : Rel A ℓ} → Decidable _∼_ → Disc (A × A) ⇒ (⊤ + ⊤)
  binPred _∼_ .at X (x , y) with x ∼ y
  ... | yes _ = inj₁ tt
  ... | no _ = inj₂ tt
  binPred _∼_ .at-resp-≈ X {x , y} ≡-refl with x ∼ y
  ... | yes _ = ≡-refl
  ... | no _ = ≡-refl
  binPred _∼_ .commute f (x , y) with x ∼ y
  ... | yes _ = ≡-refl
  ... | no _ = ≡-refl

-- Lifting
ℒ : ∀ {a} → FOApproxSetPSh a → FOApproxSetPSh a
ℒ F .obj X = F .obj (ℒₐ X)
ℒ F .map f = F .map (ℒ-map f)
ℒ F .map-resp-≈ f = F .map-resp-≈ (ℒ-map-resp-≃ f)
ℒ F .preserves-∘ {X} {Y} {Z} f g x =
  F .obj (ℒₐ X) .isEquivalence .trans
    (F .preserves-∘ (ℒ-map f) (ℒ-map g) x)
    (F .map-resp-≈ (ℒ-map-preserves-∘ f g) (F .obj (ℒₐ Z) .isEquivalence .refl))
ℒ F .preserves-id f x = F .preserves-id (ℒ-map f) x

ℒ-join : ∀ {F : FOApproxSetPSh 0ℓ} → ℒ (ℒ F) ⇒ ℒ F
ℒ-join {F} .at X = F .map ℒₐ-unit
ℒ-join {F} .at-resp-≈ X = F .map-resp-≈ (≃mₐ-setoid (ℒₐ X) _ .isEquivalence .refl)
ℒ-join {F} .commute {X} {Y} f x =
  begin
    F .map ℒₐ-unit (F .map (ℒ-map (ℒ-map f)) x)
  ≈⟨ F .preserves-∘ _ _ x ⟩
    F .map (ℒ-map (ℒ-map f) ∘ₐ ℒₐ-unit {ℒₐ X}) x
  ≈⟨ F .map-resp-≈ (≃mₐ-setoid _ _ .isEquivalence .sym (ℒ-unit-commute (ℒ-map f)))
                   (F .obj (ℒₐ (ℒₐ Y)) .isEquivalence .refl) ⟩
    F .map (ℒₐ-unit {ℒₐ Y} ∘ₐ ℒ-map f) x
  ≈⟨ F .obj (ℒₐ X) .isEquivalence .sym (F .preserves-∘ _ _ x) ⟩
    F .map (ℒ-map f) (F .map (ℒₐ-unit {ℒₐ Y}) x)
  ∎
  where open import Relation.Binary.Reasoning.Setoid (F .obj (ℒₐ X))
