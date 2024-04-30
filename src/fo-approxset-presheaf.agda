{-# OPTIONS --postfix-projections --without-K #-}

module fo-approxset-presheaf where

open import Level
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function renaming (id to idₛ; _∘_ to _∘ₛ_)
open import Relation.Binary.PropositionalEquality hiding (isEquivalence)
open import Relation.Binary using (Setoid; IsEquivalence)
open Setoid using (Carrier; _≈_; isEquivalence)
open ≡-Reasoning
open import fo-approxset using (FOApproxSet) renaming (_⇒_ to _⇒ₐ_; _≃m_ to _≃mₐ_; id to idₐ; _∘_ to _∘ₐ_; _⊗_ to _⊗ₐ_)

-- For now how we state functoriality/naturality.
infix 4 _≃mₛ_
_≃mₛ_ : ∀ {a b} {A : Set a} {B : Set b} → (A -> B) -> (A → B) -> Set (a ⊔ b)
f ≃mₛ g = ∀ x → f x ≡ g x

≈-sym : ∀ {a b} {A : Set a} {B : Set b} {f : A -> B} {g : A → B} → f ≃mₛ g → g ≃mₛ f
≈-sym f≃g x = sym (f≃g x)

-- But maybe too restrictive because then ⇒ₐ equations need to hold up to propositional equality.
postulate
  ∘ₐ-assoc : ∀ {W X Y Z} (f : Y ⇒ₐ Z) (g : X ⇒ₐ Y) (h : W ⇒ₐ X) → f ∘ₐ (g ∘ₐ h) ≡ (f ∘ₐ g) ∘ₐ h
  ∘ₐ-unitᵣ : ∀ {X Y} (f : X ⇒ₐ Y) → f ∘ₐ idₐ ≡ f
  ∘ₐ-unitₗ : ∀ {X Y} (f : X ⇒ₐ Y) → idₐ ∘ₐ f ≡ f

-- Presheaf on FOApproxSet.
record FOApproxSetPSh a : Set (suc a) where
  field
    obj : FOApproxSet → Setoid a a
    map : ∀ {X Y} → (X ⇒ₐ Y) → obj Y .Carrier → obj X .Carrier
    preserves-∘ : ∀ {X Y Z} (f : Y ⇒ₐ Z) (g : X ⇒ₐ Y) → (map g ∘ₛ map f) ≃mₛ map (f ∘ₐ g)

open FOApproxSetPSh

record _⇒_ {a b} (F : FOApproxSetPSh a) (G : FOApproxSetPSh b) : Set (suc (a ⊔ b)) where
  field
    at : ∀ (X : FOApproxSet) → F .obj X .Carrier → G .obj X .Carrier
    commute : ∀ {X Y : FOApproxSet} (f : X ⇒ₐ Y) → at X ∘ₛ F .map f ≃mₛ G .map f ∘ₛ at Y

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
(F ⊗ G) .obj X .Carrier = F .obj X .Carrier × G .obj X .Carrier
(F ⊗ G) .obj X ._≈_ (x₁ , y₁) (x₂ , y₂) = F .obj X ._≈_ x₁ x₂ × G .obj X ._≈_ y₁ y₂
(F ⊗ G) .obj X .isEquivalence .IsEquivalence.refl .proj₁ = F .obj X .isEquivalence .IsEquivalence.refl
(F ⊗ G) .obj X .isEquivalence .IsEquivalence.refl .proj₂ = G .obj X .isEquivalence .IsEquivalence.refl
(F ⊗ G) .obj X .isEquivalence .IsEquivalence.sym (x₁≈y₁ , _) .proj₁ = F .obj X .isEquivalence .IsEquivalence.sym x₁≈y₁
(F ⊗ G) .obj X .isEquivalence .IsEquivalence.sym (_ , x₂≈y₂) .proj₂ = G .obj X .isEquivalence .IsEquivalence.sym x₂≈y₂
(F ⊗ G) .obj X .isEquivalence .IsEquivalence.trans (x₁≈y₁ , _) (y₁≈z₁ , _) .proj₁ = F .obj X .isEquivalence .IsEquivalence.trans x₁≈y₁ y₁≈z₁
(F ⊗ G) .obj X .isEquivalence .IsEquivalence.trans (_ , x₂≈y₂) (_ , y₂≈z₂) .proj₂ = G .obj X .isEquivalence .IsEquivalence.trans x₂≈y₂ y₂≈z₂
(F ⊗ G) .map f (x , y) .proj₁ = F .map f x
(F ⊗ G) .map f (x , y) .proj₂ = G .map f y
(F ⊗ G) .preserves-∘ f g (x , y) = cong₂ _,_ (F .preserves-∘ f g x) (G .preserves-∘ f g y)

π₁ : ∀ {a b} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} → (F ⊗ G) ⇒ F
π₁ .at X = proj₁
π₁ .commute f _ = refl

π₂ : ∀ {a b} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} → (F ⊗ G) ⇒ G
π₂ .at X = proj₂
π₂ .commute f _ = refl

pair : ∀ {a b c} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} {H : FOApproxSetPSh c} → F ⇒ G → F ⇒ H → F ⇒ (G ⊗ H)
pair ζ η .at X x .proj₁ = ζ .at X x
pair ζ η .at X x .proj₂ = η .at X x
pair ζ η .commute f x = cong₂ _,_ (ζ .commute f x) (η .commute f x)

-- Sums
_+_ : ∀ {a} → FOApproxSetPSh a → FOApproxSetPSh a → FOApproxSetPSh a
(F + G) .obj X .Carrier = F .obj X .Carrier ⊎ G .obj X .Carrier
(F + G) .obj X ._≈_ (inj₁ x) (inj₁ y) = F .obj X ._≈_ x y
(F + G) .obj X ._≈_ (inj₂ x) (inj₂ y) = G .obj X ._≈_ x y
(F + G) .obj X ._≈_ (inj₁ x) (inj₂ y) = Lift _ 𝟘
(F + G) .obj X ._≈_ (inj₂ x) (inj₁ y) = Lift _ 𝟘
(F + G) .obj X .isEquivalence = {!   !}
(F + G) .map f (inj₁ x) = inj₁ (F .map f x)
(F + G) .map f (inj₂ x) = inj₂ (G .map f x)
(F + G) .preserves-∘ f g (inj₁ x) = cong inj₁ (F .preserves-∘ f g x)
(F + G) .preserves-∘ f g (inj₂ x) = cong inj₂ (G .preserves-∘ f g x)

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

-- Yoneda embedding Y ↦ Hom(-, Y)
よ : FOApproxSet -> FOApproxSetPSh 0ℓ
よ Y .obj X .Carrier = X ⇒ₐ Y
よ Y .obj X ._≈_ = {!   !}
よ Y .obj X .isEquivalence = {!   !}
よ Y .map f g = g ∘ₐ f
よ Y .preserves-∘ f g h = sym (∘ₐ-assoc h f g)

-- Functions. (F ⊗ よ X) ⇒ G and よ X ⇒ (F ⊸ G) are isomorphic
_⊸_ : ∀ {a b} → FOApproxSetPSh a → FOApproxSetPSh b → FOApproxSetPSh (suc (a ⊔ b))
(F ⊸ G) .obj X .Carrier = (F ⊗ よ X) ⇒ G
(F ⊸ G) .obj X ._≈_ = {!   !}
(F ⊸ G) .obj X .isEquivalence = {!   !}
(F ⊸ G) .map f η .at X (x , g) = η .at X (x , f ∘ₐ g)
(F ⊸ G) .map f η .commute {W} {Z} g (x , h) =
  begin
    η .at W (F .map g x , f ∘ₐ (h ∘ₐ g))
  ≡⟨ cong (λ f' → η .at W (F .map g x , f')) (∘ₐ-assoc f h g) ⟩
    η .at W (F .map g x , (f ∘ₐ h) ∘ₐ g)
  ≡⟨ η .commute g (x , f ∘ₐ h) ⟩
    G .map g (η .at Z (x , f ∘ₐ h))
  ∎
(F ⊸ G) .preserves-∘ f g η =
  begin
    (F ⊸ G) .map g ((F ⊸ G) .map f η)
  ≡⟨ {!   !} ⟩ -- need to show natural transformations are equivalent
    (F ⊸ G) .map (f ∘ₐ g) η
  ∎

eval : ∀ {a b} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} → ((F ⊸ G) ⊗ F) ⇒ G
eval .at X (η , x) = η .at X (x , idₐ)
eval {F = F} {G} .commute {X} {Y} f (η , y) =
  begin
    η .at X (F .map f y , f ∘ₐ idₐ)
  ≡⟨ cong (λ f' → η .at X (F .map f y , f')) (trans (∘ₐ-unitᵣ f) (sym (∘ₐ-unitₗ f))) ⟩
    η .at X ((F ⊗ よ Y) .map f (y , idₐ))
  ≡⟨ η .commute f (y , idₐ) ⟩
    G .map f (η .at Y (y , idₐ))
  ∎

lambda : ∀ {a b c} {F : FOApproxSetPSh a} {G : FOApproxSetPSh b} {H : FOApproxSetPSh c} → (F ⊗ G) ⇒ H → F ⇒ (G ⊸ H)
lambda {F = F} η .at X x .at Y (y , f) = η .at Y (F .map f x , y)
lambda {F = F} {G} {H} η .at X x .commute {Y} {Z} f (z , g) =
  begin
    η .at Y (F .map (g ∘ₐ f) x , G .map f z)
  ≡⟨ cong (λ y → η .at Y (y , G .map f z)) (≈-sym (F .preserves-∘ g f) x) ⟩
    η .at Y (F .map f (F .map g x) , G .map f z)
  ≡⟨ η .commute f (F .map g x , z) ⟩
    H .map f (η .at Z (F .map g x , z))
  ∎
lambda {F = F} {G} {H} η .commute {X} {Y} f x =
  begin
    lambda η .at X (F .map f x)
  ≡⟨ {!   !} ⟩ -- need to show natural transformations are equivalent
    (G ⊸ H) .map f (lambda η .at Y x)
  ∎
