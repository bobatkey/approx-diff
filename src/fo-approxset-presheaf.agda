{-# OPTIONS --postfix-projections --safe --without-K #-}

module fo-approxset-presheaf where

open import Level
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function renaming (id to idₛ; _∘_ to _∘ₛ_)
open import Relation.Binary using (Setoid; IsEquivalence; Transitive)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; _≡_; setoid) renaming (refl to ≡-refl; trans to ≡-trans; sym to ≡-sym)
open IsEquivalence
open Setoid using (Carrier; _≈_; isEquivalence)
import Relation.Binary.Reasoning.Setoid
open import basics
open import fo-approxset
    using (FOApproxSet; ℒ; ℒ-map; ℒ-map-resp-≃; ℒ-preserves-∘; ℒ-unit; ℒ-unit-commute; ℒ-join; ℒ-join-commute)
    renaming (
      _⇒_ to _⇒ₐ_; _≃m_ to _≃mₐ_; ≃m-setoid to ≃mₐ-setoid; id to idₐ; _∘_ to _∘ₐ_; _⊗_ to _⊗ₐ_;
      ∘-resp-≃m to ∘ₐ-resp-≃m; ∘-assoc to ∘ₐ-assoc; ∘-unitₗ to ∘ₐ-unitₗ; ∘-unitᵣ to ∘ₐ-unitᵣ
    )

module ≃-Reasoning = Relation.Binary.Reasoning.Setoid

module _ {X Y : FOApproxSet} where
  open IsEquivalence (≃mₐ-setoid {X} {Y} .isEquivalence)
    renaming (refl to ≃mₐ-refl; sym to ≃mₐ-sym; trans to ≃mₐ-trans) public

-- Presheaf on FOApproxSet.
record FOApproxSetPSh a : Set (suc a) where
  field
    obj : FOApproxSet → Setoid a a
    map : ∀ {X Y} → (X ⇒ₐ Y) → obj Y .Carrier → obj X .Carrier
    map-resp-≈ : ∀ {X Y} {f f' : X ⇒ₐ Y} → f ≃mₐ f' → ∀ {x y} → obj Y ._≈_ x y → obj X ._≈_ (map f x) (map f' y)
    preserves-∘ : ∀ {X Y Z} {f : Y ⇒ₐ Z} {g : X ⇒ₐ Y} → ∀ x → obj X ._≈_ (map g (map f x)) (map (f ∘ₐ g) x)
    preserves-id : ∀ {X Y} {f : X ⇒ₐ Y} → ∀ x → obj X ._≈_ (idₛ (map f x)) (map f (idₛ x))

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
  ≃m-setoid : ∀ {a b} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} → Setoid (suc (a ⊔ b)) (suc (a ⊔ b))
  ≃m-setoid {F = F} {G} .Carrier = F ⇒ G
  ≃m-setoid ._≈_ η ζ = η ≃m ζ
  ≃m-setoid .isEquivalence .refl {η} .eqat X x = η .at-resp-≈ X x
  ≃m-setoid {F = F} {G} .isEquivalence .sym η≃ζ .eqat X x =
    G .obj X .isEquivalence .sym (η≃ζ .eqat X (F .obj X .isEquivalence .sym x))
  ≃m-setoid {F = F} {G} .isEquivalence .trans η≃ζ ζ≃ε .eqat X x =
    G .obj X .isEquivalence .trans (η≃ζ .eqat X x) (ζ≃ε .eqat X (F .obj X .isEquivalence .refl))

-- Definitions for category
id : ∀ {a} {F : FOApproxSetPSh a} → F ⇒ F
id .at X = idₛ
id .at-resp-≈ X = idₛ
id {F = F} .commute f = F .preserves-id

_∘_ : ∀ {a b c} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} {H : FOApproxSetPSh c} → G ⇒ H → F ⇒ G → F ⇒ H
(ζ ∘ η) .at X = ζ .at X ∘ₛ η .at X
(ζ ∘ η) .at-resp-≈ X = ζ .at-resp-≈ X ∘ₛ η .at-resp-≈ X
_∘_ {H = H} ζ η .commute {X} {Y} f y =
  H .obj X .isEquivalence .trans (ζ .at-resp-≈ X (η .commute f y)) (ζ .commute f (η .at Y y))

∘-resp-≃m : ∀ {a b c} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} {H : FOApproxSetPSh c} →
            ∀ {η η' : G ⇒ H} → ∀ {ζ ζ' : F ⇒ G} → η ≃m η' → ζ ≃m ζ' → (η ∘ ζ) ≃m (η' ∘ ζ')
∘-resp-≃m η ζ .eqat X x = η .eqat X (ζ .eqat X x)

infixr 10 _∘_

-- Terminal object
module _ where
  open import Data.Unit.Properties using () renaming (≡-setoid to 𝟙) public

  ⊤ : FOApproxSetPSh 0ℓ
  ⊤ .obj X = 𝟙
  ⊤ .map f _ = tt
  ⊤ .map-resp-≈ f _ = 𝟙 .isEquivalence .refl
  ⊤ .preserves-∘ _ = 𝟙 .isEquivalence .refl
  ⊤ .preserves-id _ = 𝟙 .isEquivalence .refl

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
(F ⊗ G) .preserves-∘ (x , y) .proj₁ = F .preserves-∘ x
(F ⊗ G) .preserves-∘ (x , y) .proj₂ = G .preserves-∘ y
(F ⊗ G) .preserves-id (x , y) .proj₁ = F .preserves-id x
(F ⊗ G) .preserves-id (x , y) .proj₂ = G .preserves-id y

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
(F + G) .preserves-∘ (inj₁ x) = F .preserves-∘ x
(F + G) .preserves-∘ (inj₂ x) = G .preserves-∘ x
(F + G) .preserves-id (inj₁ x) = F .preserves-id x
(F + G) .preserves-id (inj₂ x) = G .preserves-id x

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
よ Y .obj X = ≃mₐ-setoid {X = X} {Y}
よ Y .map f g = g ∘ₐ f
よ Y .map-resp-≈ f g = ∘ₐ-resp-≃m g f
よ Y .preserves-∘ {X} {f = f} {g} h = ≃mₐ-sym (∘ₐ-assoc h f g)
よ Y .preserves-id {X} {f = f} g =
  ≃mₐ-trans (≡-to-≈ ≃mₐ-setoid ≡-refl) (≡-to-≈ ≃mₐ-setoid (cong (λ g' → g' ∘ₐ f) {y = g} ≡-refl))

-- Functions. (F ⊗ よ X) ⇒ G and よ X ⇒ (F ⊸ G) are isomorphic
_⊸_ : ∀ {a b} → FOApproxSetPSh a → FOApproxSetPSh b → FOApproxSetPSh (suc (a ⊔ b))
(F ⊸ G) .obj X = ≃m-setoid {F = F ⊗ よ X} {G}
(F ⊸ G) .map f η .at X (x , g) = η .at X (x , f ∘ₐ g)
(F ⊸ G) .map f η .at-resp-≈ X (x , g) =
  η .at-resp-≈ X (x , ∘ₐ-resp-≃m {f = f} ≃mₐ-refl g)
(F ⊸ G) .map f η .commute {Y} {Z} g (x , h) =
  G .obj Y .isEquivalence .trans
    (η .at-resp-≈ Y (F .obj Y .isEquivalence .refl , ∘ₐ-assoc f h g)) (η .commute g (x , f ∘ₐ h))
(F ⊸ G) .map-resp-≈ f η .eqat X (x , g) = η .eqat X (x , ∘ₐ-resp-≃m f g)
(F ⊸ G) .preserves-∘ {Y} {Z = Z} {f = f} {g} η .eqat X {_ , h₁} (x , h) =
  η .at-resp-≈ X (x , ≃mₐ-trans (∘ₐ-assoc f g h₁) (∘ₐ-resp-≃m {f = f ∘ₐ g} ≃mₐ-refl h))
(F ⊸ G) .preserves-id {Y} {Z} {f = f} η .eqat X (x , h) =
  η .at-resp-≈ X (x , ∘ₐ-resp-≃m {f = f} ≃mₐ-refl h)

eval : ∀ {a b} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} → ((F ⊸ G) ⊗ F) ⇒ G
eval .at X (η , x) = η .at X (x , idₐ)
eval .at-resp-≈ X (η , x) = η .eqat X (x , ≃mₐ-setoid .isEquivalence .refl)
eval {F = F} {G} .commute {X} {Y} f (η , y) =
  G .obj X .isEquivalence .trans
    (η .at-resp-≈ X (F .obj X .isEquivalence .refl , ≃mₐ-trans (∘ₐ-unitᵣ f) (≃mₐ-sym (∘ₐ-unitₗ f))))
    (η .commute f (y , idₐ))

lambda : ∀ {a b c} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} {H : FOApproxSetPSh c} → (F ⊗ G) ⇒ H → F ⇒ (G ⊸ H)
lambda {F = F} η .at X x .at Y (y , f) = η .at Y (F .map f x , y)
lambda {F = F} η .at X x .at-resp-≈ Y (y , f) =
  η .at-resp-≈ Y (F .map-resp-≈ f (F .obj X .isEquivalence .refl) , y)
lambda {F = F} {G} {H} η .at X x .commute {Y} {Z} f (z , g) =
  H .obj Y .isEquivalence .trans
    (η .at-resp-≈ Y (F .obj Y .isEquivalence .sym (F .preserves-∘ x) , G .obj Y .isEquivalence .refl))
    (η .commute f (F .map g x , z))
lambda {F = F} {G} η .at-resp-≈ X x .eqat Y (y , f) = η .at-resp-≈ Y (F .map-resp-≈ f x , y)
lambda {F = F} {G} η .commute {X} {Y} f x .eqat Z (z , g) =
  η .at-resp-≈ Z (
    F .obj Z .isEquivalence .trans
      (F .preserves-∘ x)
      (F .map-resp-≈ (∘ₐ-resp-≃m {f = f} ≃mₐ-refl g) (F .obj Y .isEquivalence .refl)) ,
    z
  )

-- TODO: verify law relating eval and lambda

-- Any old set becomes a constant presheaf
Disc : Set → FOApproxSetPSh 0ℓ
Disc A .obj X = setoid A
Disc A .map f = idₛ
Disc A .map-resp-≈ f = idₛ
Disc A .preserves-∘ x = ≡-refl
Disc A .preserves-id x = ≡-refl

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

-- Y ↦ Hom(ℒ -, Y)
よℒ : FOApproxSet → FOApproxSetPSh 0ℓ
よℒ Y .obj X = ≃mₐ-setoid {X = ℒ X} {Y}
よℒ Y .map f g = g ∘ₐ ℒ-map f
よℒ Y .map-resp-≈ f {g₁} g = ∘ₐ-resp-≃m {f = g₁} g (ℒ-map-resp-≃ f)
よℒ Y .preserves-∘ {f = f} {g = g} h =
  ≃mₐ-trans (≃mₐ-sym (∘ₐ-assoc h (ℒ-map f) (ℒ-map g))) (∘ₐ-resp-≃m {f = h} ≃mₐ-refl ℒ-preserves-∘)
よℒ Y .preserves-id f = ≡-to-≈ ≃mₐ-setoid ≡-refl

-- Direct image functor for the monad ℒ, which is also a monad. (However I think this is the right Kan
-- extension, not the left, i.e. right adjoint to inverse image functor for ℒ, whereas we want left adjoint.)
ℒ* : ∀ {a} → FOApproxSetPSh a → FOApproxSetPSh (suc a)
ℒ* F .obj X = ≃m-setoid {F = よℒ X} {F}
ℒ* F .map f η .at X g = η .at X (f ∘ₐ g)
ℒ* F .map f η .at-resp-≈ X g = η .at-resp-≈ X (∘ₐ-resp-≃m {f = f} ≃mₐ-refl g)
ℒ* F .map f η .commute {X} g h =
  F .obj X .isEquivalence .trans (η .at-resp-≈ X (∘ₐ-assoc f h (ℒ-map g))) (η .commute g (f ∘ₐ h))
ℒ* F .map-resp-≈ f η .eqat X g = η .eqat X (∘ₐ-resp-≃m f g)
ℒ* F .preserves-∘ {f = f} {g} η .eqat X {h₁} h =
  F .obj X .isEquivalence .trans
    (η .at-resp-≈ X (∘ₐ-assoc f g h₁))
    (η .at-resp-≈ X (∘ₐ-resp-≃m {f = f ∘ₐ g} ≃mₐ-refl h))
ℒ* F .preserves-id {f = f} η .eqat X {g₁} {g₂} g =
  η .at-resp-≈ X (∘ₐ-resp-≃m {f = f} ≃mₐ-refl g)

ℒ*-map : ∀ {a} {F G : FOApproxSetPSh a} → F ⇒ G → ℒ* F ⇒ ℒ* G
ℒ*-map η .at X ζ = η ∘ ζ
ℒ*-map η .at-resp-≈ X ζ = ∘-resp-≃m {η = η} (≃m-setoid .isEquivalence .refl) ζ
ℒ*-map {G = G} η .commute f ζ .eqat X g =
  η .at-resp-≈ X (ζ .at-resp-≈ X (∘ₐ-resp-≃m {f = f} ≃mₐ-refl g))

ℒ*-unit : ∀ {a} {F : FOApproxSetPSh a} → F ⇒ ℒ* F
ℒ*-unit {F = F} .at X x .at Y f = F .map ℒ-unit (F .map f x)
ℒ*-unit {F = F} .at X x .at-resp-≈ Y f =
  F .map-resp-≈ ≃mₐ-refl (F .map-resp-≈ f (F .obj X .isEquivalence .refl))
ℒ*-unit {F = F} .at X x .commute {Y} {Z} f g =
  begin
    F .map ℒ-unit (F .map (g ∘ₐ ℒ-map f) x)
  ≈⟨ F .map-resp-≈ ≃mₐ-refl (F .obj (ℒ Y) .isEquivalence .sym (F .preserves-∘ x)) ⟩
    F .map ℒ-unit (F .map (ℒ-map f) (F .map g x))
  ≈⟨ F .preserves-∘ (F .map g x) ⟩
    F .map (ℒ-map f ∘ₐ ℒ-unit) (F .map g x)
  ≈⟨ F .map-resp-≈ (≃mₐ-sym (ℒ-unit-commute f)) (F .obj (ℒ Z) .isEquivalence .refl) ⟩
    F .map (ℒ-unit ∘ₐ f) (F .map g x)
  ≈⟨ F .obj Y .isEquivalence .sym (F .preserves-∘ (F .map g x)) ⟩
    F .map f (F .map ℒ-unit (F .map g x))
  ∎
  where open ≃-Reasoning (F .obj Y)
ℒ*-unit {F = F} .at-resp-≈ X x .eqat Y f =
  F .map-resp-≈ ≃mₐ-refl (F .map-resp-≈ f x)
ℒ*-unit {F = F} .commute {Y} {Z} f x .eqat X g =
  F .map-resp-≈ ≃mₐ-refl
  (F .obj (ℒ X) .isEquivalence .trans
    (F .preserves-∘ x)
    (F .map-resp-≈ (∘ₐ-resp-≃m {f = f} ≃mₐ-refl g) (F .obj Z .isEquivalence .refl)))

ℒ*-join : ∀ {a} {F : FOApproxSetPSh a} → ℒ* (ℒ* F) ⇒ ℒ* F
ℒ*-join {F = F} .at X η .at Z f = F .map ℒ-unit (η .at (ℒ Z) (f ∘ₐ ℒ-join) .at (ℒ Z) ℒ-join)
ℒ*-join {F = F} .at X η .at-resp-≈ Z f =
  F .map-resp-≈ ≃mₐ-refl
    (η .at-resp-≈ (ℒ Z) (∘ₐ-resp-≃m {g = ℒ-join} f ≃mₐ-refl) .eqat (ℒ Z) ≃mₐ-refl)
ℒ*-join {F = F} .at X η .commute {Y} {Z} f g =
  begin
    F .map ℒ-unit (η .at (ℒ Y) ((g ∘ₐ ℒ-map f) ∘ₐ ℒ-join) .at (ℒ Y) ℒ-join)
  ≈⟨ F .map-resp-≈ ≃mₐ-refl (η .at-resp-≈ (ℒ Y) (≃mₐ-sym (∘ₐ-assoc g (ℒ-map f) ℒ-join)) .eqat (ℒ Y) ≃mₐ-refl ) ⟩
    F .map ℒ-unit (η .at (ℒ Y) (g ∘ₐ (ℒ-map f ∘ₐ ℒ-join)) .at (ℒ Y) ℒ-join)
  ≈⟨ F .map-resp-≈ ≃mₐ-refl (η .at-resp-≈ (ℒ Y) (∘ₐ-resp-≃m {f = g} ≃mₐ-refl (≃mₐ-sym (ℒ-join-commute f))) .eqat (ℒ Y) ≃mₐ-refl ) ⟩
    F .map ℒ-unit (η .at (ℒ Y) (g ∘ₐ ℒ-join ∘ₐ ℒ-map (ℒ-map f)) .at (ℒ Y) ℒ-join)
  ≈⟨ F .map-resp-≈ ≃mₐ-refl (η .at-resp-≈ (ℒ Y) (∘ₐ-assoc g ℒ-join (ℒ-map (ℒ-map f))) .eqat (ℒ Y) ≃mₐ-refl) ⟩
    F .map ℒ-unit (η .at (ℒ Y) ((g ∘ₐ ℒ-join) ∘ₐ ℒ-map (ℒ-map f)) .at (ℒ Y) ℒ-join)
  ≈⟨ F .map-resp-≈ ≃mₐ-refl (η .commute (ℒ-map f) (g ∘ₐ ℒ-join) .eqat (ℒ Y) ≃mₐ-refl) ⟩
    F .map ℒ-unit (η .at (ℒ Z) (g ∘ₐ ℒ-join) .at (ℒ Y) (ℒ-map f ∘ₐ ℒ-join))
  ≈⟨ F .map-resp-≈ ≃mₐ-refl (η .at-resp-≈ (ℒ Z) ≃mₐ-refl .eqat (ℒ Y) (≃mₐ-sym (ℒ-join-commute f))) ⟩
    F .map ℒ-unit (η .at (ℒ Z) (g ∘ₐ ℒ-join) .at (ℒ Y) (ℒ-join ∘ₐ ℒ-map (ℒ-map f)))
  ≈⟨ F .map-resp-≈ ≃mₐ-refl (η .at (ℒ Z) (g ∘ₐ ℒ-join) .commute (ℒ-map f) ℒ-join) ⟩
    F .map ℒ-unit (F .map (ℒ-map f) (η .at (ℒ Z) (g ∘ₐ ℒ-join) .at (ℒ Z) ℒ-join))
  ≈⟨ F .preserves-∘ _ ⟩
    F .map (ℒ-map f ∘ₐ ℒ-unit) (η .at (ℒ Z) (g ∘ₐ ℒ-join) .at (ℒ Z) ℒ-join)
  ≈⟨ F .map-resp-≈ (≃mₐ-sym (ℒ-unit-commute _)) (F .obj (ℒ Z) .isEquivalence .refl) ⟩
    F .map (ℒ-unit ∘ₐ f) (η .at (ℒ Z) (g ∘ₐ ℒ-join) .at (ℒ Z) ℒ-join)
  ≈⟨ F .obj Y .isEquivalence .sym (F .preserves-∘ _) ⟩
    F .map f (F .map ℒ-unit (η .at (ℒ Z) (g ∘ₐ ℒ-join) .at (ℒ Z) ℒ-join))
  ∎
  where open ≃-Reasoning (F .obj Y)
ℒ*-join {F = F} .at-resp-≈ X η .eqat Z f =
  F .map-resp-≈ ≃mₐ-refl (η .eqat (ℒ Z) (∘ₐ-resp-≃m {g = ℒ-join} f ≃mₐ-refl) .eqat (ℒ Z) ≃mₐ-refl)
ℒ*-join {F = F} .commute f g .eqat Z {h₁} {h₂} h =
  begin
    F .map ℒ-unit (g .at (ℒ Z) (f ∘ₐ h₁ ∘ₐ ℒ-join) .at (ℒ Z) ℒ-join)
  ≈⟨ F .map-resp-≈ ≃mₐ-refl (g .at-resp-≈ (ℒ Z) (∘ₐ-assoc f h₁ ℒ-join) .eqat (ℒ Z) ≃mₐ-refl) ⟩
    F .map ℒ-unit (g .at (ℒ Z) ((f ∘ₐ h₁) ∘ₐ ℒ-join) .at (ℒ Z) ℒ-join)
  ≈⟨ F .map-resp-≈ ≃mₐ-refl (g .at-resp-≈ (ℒ Z) (∘ₐ-resp-≃m {g = ℒ-join} (∘ₐ-resp-≃m {f = f} ≃mₐ-refl h) ≃mₐ-refl) .eqat (ℒ Z) ≃mₐ-refl) ⟩
    F .map ℒ-unit (g .at (ℒ Z) ((f ∘ₐ h₂) ∘ₐ ℒ-join) .at (ℒ Z) ℒ-join)
  ∎
  where open ≃-Reasoning (F .obj Z)

-- TODO: verify monad laws

ℒ*-strength : ∀ {a b} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} → (F ⊗ ℒ* G) ⇒ ℒ* (F ⊗ G)
ℒ*-strength {F = F} .at X (x , η) .at Y f .proj₁ = F .map ℒ-unit (F .map f x)
ℒ*-strength .at X (x , η) .at Y f .proj₂ = η .at Y f
ℒ*-strength {F = F} .at X (x , η) .at-resp-≈ Y f .proj₁ =
  F .map-resp-≈ ≃mₐ-refl (F .map-resp-≈ f (F .obj X .isEquivalence .refl))
ℒ*-strength .at X (x , η) .at-resp-≈ Y f .proj₂ = η .at-resp-≈ Y f
ℒ*-strength {F = F} .at X (x , η) .commute {Y} {Z} f g .proj₁ =
  begin
    F .map ℒ-unit (F .map (g ∘ₐ ℒ-map f) x)
  ≈⟨ F .preserves-∘ _ ⟩
    F .map ((g ∘ₐ ℒ-map f) ∘ₐ ℒ-unit) x
  ≈⟨ F .map-resp-≈ (≃mₐ-sym (∘ₐ-assoc g (ℒ-map f) ℒ-unit)) (F .obj X .isEquivalence .refl) ⟩
    F .map (g ∘ₐ (ℒ-map f ∘ₐ ℒ-unit)) x
  ≈⟨ F .map-resp-≈ (∘ₐ-resp-≃m {f = g} ≃mₐ-refl (≃mₐ-sym (ℒ-unit-commute _))) (F .obj X .isEquivalence .refl) ⟩
    F .map (g ∘ₐ (ℒ-unit ∘ₐ f)) x
  ≈⟨ F .obj Y .isEquivalence .sym (F .obj Y .isEquivalence .trans (F .preserves-∘ _) (F .preserves-∘ _) ) ⟩
    F .map f (F .map ℒ-unit (F .map g x))
  ∎ where open ≃-Reasoning (F .obj Y)
ℒ*-strength .at X (x , η) .commute f g .proj₂ = η .commute f g
ℒ*-strength {F = F} .at-resp-≈ X (x , η) .eqat Y f .proj₁ = F .map-resp-≈ ≃mₐ-refl (F .map-resp-≈ f x)
ℒ*-strength .at-resp-≈ X (x , η) .eqat Y f .proj₂ = η .eqat Y f
ℒ*-strength {F = F} .commute {Y} {Z} f (x , η) .eqat X {g₁} {g₂} g .proj₁ =
  F .map-resp-≈ ≃mₐ-refl
    (F .obj (ℒ X) .isEquivalence .trans (F .preserves-∘ _)
      (F .map-resp-≈ (∘ₐ-resp-≃m {f = f} ≃mₐ-refl g) (F .obj Z .isEquivalence .refl)))
ℒ*-strength .commute f (x , η) .eqat X g .proj₂ = η .at-resp-≈ X (∘ₐ-resp-≃m {f = f} ≃mₐ-refl g)

{- Inverse image functor for the monad ℒ, which is a comonad. Retained here for reference.
ℒ : ∀ {a} → FOApproxSetPSh a → FOApproxSetPSh a
ℒ F .obj X = F .obj (ℒ X)
ℒ F .map f = F .map (ℒ-map f)
ℒ F .map-resp-≈ f = F .map-resp-≈ (ℒ-map-resp-≃ f)
ℒ F .preserves-∘ {X} {Y} {Z} x =
  F .obj (ℒ X) .isEquivalence .trans
    (F .preserves-∘ x) (F .map-resp-≈ ℒ-map-preserves-∘ (F .obj (ℒ Z) .isEquivalence .refl))
ℒ F .preserves-id x = F .preserves-id x

ℒ-map : ∀ {a} {F G : FOApproxSetPSh a} → F ⇒ G → ℒ F ⇒ ℒ G
ℒ-map {F = F} η .at X = η .at (ℒ X)
ℒ-map {F = F} η .at-resp-≈ X = η .at-resp-≈ (ℒ X)
ℒ-map {F = F} {G} η .commute f x = η .commute (ℒ-map f) x

ℒ-counit : ∀ {a} {F : FOApproxSetPSh a} → ℒ F ⇒ F
ℒ-counit {F = F} .at X = F .map ℒ-unit
ℒ-counit {F = F} .at-resp-≈ X = F .map-resp-≈ ≃mₐ-refl
ℒ-counit {F = F} .commute {X} f x =
  begin
    F .map ℒ-unit (F .map (ℒ-map f) x)
  ≈⟨ F .preserves-∘ x ⟩
    F .map (ℒ-map f ∘ₐ ℒ-unit) x
  ≈⟨ F .map-resp-≈ (≃mₐ-sym (ℒ-unit-commute f)) (F .obj _ .isEquivalence .refl) ⟩
    F .map (ℒ-unit ∘ₐ f) x
  ≈⟨ F .obj X .isEquivalence .sym (F .preserves-∘ x) ⟩
    F .map f (F .map ℒ-unit x)
  ∎
  where open ≃-Reasoning (F .obj X)

ℒ-dup : ∀ {a} {F : FOApproxSetPSh a} → ℒ F ⇒ ℒ (ℒ F)
ℒ-dup {F = F} .at X = F .map ℒ-join
ℒ-dup {F = F} .at-resp-≈ X = F .map-resp-≈ ≃mₐ-refl
ℒ-dup {F = F} .commute {X} {Y} f x =
  begin
    F .map ℒ-join (F .map (ℒ-map f) x)
  ≈⟨ F .preserves-∘ x ⟩
    F .map (ℒ-map f ∘ₐ ℒ-join) x
  ≈⟨ F .map-resp-≈ (≃mₐ-sym (ℒ-join-commute _)) (F .obj (ℒ Y) .isEquivalence .refl) ⟩
    F .map (ℒ-join ∘ₐ ℒ-map (ℒ-map f)) x
  ≈⟨ F .obj (ℒ (ℒ X)) .isEquivalence .sym (F .preserves-∘ x) ⟩
    F .map (ℒ-map (ℒ-map f)) (F .map ℒ-join x)
  ∎
  where open ≃-Reasoning (F .obj (ℒ (ℒ X)))

ℒ-costrength : ∀ {a b} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} → ℒ (F ⊗ G) ⇒ (F ⊗ ℒ G)
ℒ-costrength {F = F} .at Z (x , y) = F .map ℒ-unit x , y
ℒ-costrength {F = F} .at-resp-≈ Z (x , y) = F .map-resp-≈ ≃mₐ-refl x , y
ℒ-costrength {F = F} {G} .commute {X} {Y} f (x , y) .proj₁ =
  begin
    F .map ℒ-unit (F .map (ℒ-map f) x)
  ≈⟨ F .preserves-∘ x ⟩
    F .map (ℒ-map f ∘ₐ ℒ-unit) x
  ≈⟨ F .map-resp-≈ (≃mₐ-sym (ℒ-unit-commute f)) (F .obj _ .isEquivalence .refl) ⟩
    F .map (ℒ-unit ∘ₐ f) x
  ≈⟨ F .obj X .isEquivalence .sym (F .preserves-∘ x) ⟩
    F .map f (F .map ℒ-unit x)
  ∎
  where open ≃-Reasoning (F .obj X)
ℒ-costrength {G = G} .commute {X} f (x , y) .proj₂ = G .obj (ℒ X) .isEquivalence .refl
-}
