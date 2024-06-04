{-# OPTIONS --postfix-projections --safe --without-K #-}

module basics where

open import Level
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Setoid; IsEquivalence)
import Relation.Binary.Reasoning.Setoid

module ≃-Reasoning = Relation.Binary.Reasoning.Setoid

-- Some setoid gunk that is probably in stdlib somewhere
module _ where
  open Setoid
  open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
  open IsEquivalence

  ≡-to-≈ : ∀ {a b} (X : Setoid a b) {x y : X .Carrier} → x ≡ y → X ._≈_ x y
  ≡-to-≈ X {x} {.x} ≡-refl = X .isEquivalence .refl

  ⊗-setoid : ∀ {a b c d} → Setoid a b → Setoid c d → Setoid (a ⊔ c) (b ⊔ d)
  ⊗-setoid X Y .Carrier = X .Carrier × Y .Carrier
  ⊗-setoid X Y ._≈_ (x₁ , y₁) (x₂ , y₂) = X ._≈_ x₁ x₂ × Y ._≈_ y₁ y₂
  ⊗-setoid X Y .isEquivalence .refl .proj₁ = X .isEquivalence .refl
  ⊗-setoid X Y .isEquivalence .refl .proj₂ = Y .isEquivalence .refl
  ⊗-setoid X Y .isEquivalence .sym (x₁≈y₁ , _) .proj₁ = X .isEquivalence .sym x₁≈y₁
  ⊗-setoid X Y .isEquivalence .sym (_ , x₂≈y₂) .proj₂ = Y .isEquivalence .sym x₂≈y₂
  ⊗-setoid X Y .isEquivalence .trans (x₁≈y₁ , _) (y₁≈z₁ , _) .proj₁ = X .isEquivalence .trans x₁≈y₁ y₁≈z₁
  ⊗-setoid X Y .isEquivalence .trans (_ , x₂≈y₂) (_ , y₂≈z₂) .proj₂ = Y .isEquivalence .trans x₂≈y₂ y₂≈z₂

  +-setoid : ∀ {a b} (X : Setoid a b) (Y : Setoid a b) → Setoid a b
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

  record _⇒_ {a b} (X Y : Setoid a b) : Set (a ⊔ b) where
    field
      func : X .Carrier → Y .Carrier
      func-resp-≈ : ∀ {x y} → X ._≈_ x y → Y ._≈_ (func x) (func y)

  open _⇒_

  record _≃m_ {a b} {X Y : Setoid a b} (f g : X ⇒ Y) : Set (suc (a ⊔ b)) where
    field
      eqfunc : ∀ x → Y ._≈_ (f .func x) (g .func x)

  open _≃m_

  id : ∀ {a b} {X : Setoid a b} → X ⇒ X
  id .func x = x
  id .func-resp-≈ x = x

  _∘_ : ∀ {a b} {X Y Z : Setoid a b} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
  (f ∘ g) .func x = f .func (g .func x)
  (f ∘ g) .func-resp-≈ x = f .func-resp-≈ (g .func-resp-≈ x)

  record Iso {a b} (X Y : Setoid a b) : Set (suc (a ⊔ b)) where
    field
      right : X ⇒ Y
      left : Y ⇒ X
      isoᵣ : (right ∘ left) ≃m id
      isoₗ : (left ∘ right) ≃m id

  -- Each proof p : i = j gives rise to an extensional "reindexing" bijection φ p : X i → X j.
  record Resp-≈ {a b} (I : Setoid a b) (X : I .Carrier → Setoid a b) : Set (suc (a ⊔ b)) where
    open Iso
    field
      eq : ∀ {i j} → I ._≈_ i j → Iso (X i) (X j)
      eq-refl : ∀ {i} → (eq (I .isEquivalence .refl {i}) .right) ≃m id
      eq-trans : ∀ {i j k} (p : I ._≈_ i j) (q : I ._≈_ j k) (r : I ._≈_ i k) →
                 (eq q .right ∘ eq p .right) ≃m eq r .right

  open Resp-≈

  -- Coproduct of setoid-indexed family of setoids.
  ∐-setoid : ∀ {a b} (I : Setoid a b) (X : I .Carrier → Setoid a b) → Resp-≈ I X → Setoid a b
  ∐-setoid I X resp-≈ .Carrier = Σ (I .Carrier) λ i → X i .Carrier
  ∐-setoid I X resp-≈ ._≈_ (i , x) (j , y) =
    Σ (I ._≈_ i j) λ p → X j ._≈_ (resp-≈ .eq p .Iso.right .func x) y
  ∐-setoid I X resp-≈ .isEquivalence .refl {i , x} =
    I .isEquivalence .refl , resp-≈ .eq-refl {i} .eqfunc x
  ∐-setoid I X resp-≈ .isEquivalence .sym = {!   !}
  ∐-setoid I X resp-≈ .isEquivalence .trans {i , x} {j , y} {k , z} (i≈j , x≈y) (j≈k , y≈z) =
    I .isEquivalence .trans i≈j j≈k , {!   !}

-- Also should be in stdlib somewhere
module _ where
  infix 4 _⇔_

  _⇔_ : Set → Set → Set
  P ⇔ Q = (P → Q) × (Q → P)

module _ {a} {A : Set a} where

  SymmetricClosure : ∀ {b} → (A → A → Set b) → (A → A → Set b)
  SymmetricClosure R x y = R x y × R y x

  record IsPreorder {b} (_≤_ : A → A → Set b) : Set (a ⊔ b) where
    field
      refl  : ∀ {x} → x ≤ x
      trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    _≃_ = SymmetricClosure _≤_
    infix 4 _≃_

module _ {a b} {A : Set a} {_≤_ : A → A → Set b} (≤-isPreorder : IsPreorder _≤_) where

  module _ where
    open IsPreorder ≤-isPreorder

    isEquivalenceOf : IsEquivalence (SymmetricClosure _≤_)
    isEquivalenceOf .IsEquivalence.refl = refl , refl
    isEquivalenceOf .IsEquivalence.sym (x≤y , y≤x) = y≤x , x≤y
    isEquivalenceOf .IsEquivalence.trans (x≤y , y≤x) (y≤z , z≤y) =
      (trans x≤y y≤z) , (trans z≤y y≤x)

    setoidOf : Setoid a b
    setoidOf .Setoid.Carrier = A
    setoidOf .Setoid._≈_ = SymmetricClosure _≤_
    setoidOf .Setoid.isEquivalence = isEquivalenceOf

  record IsMonoid (_∙_ : A → A → A) (ε : A) : Set (a ⊔ b) where
    open IsPreorder ≤-isPreorder
    field
      mono  : ∀ {x₁ y₁ x₂ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ ∙ y₁) ≤ (x₂ ∙ y₂)
      assoc : ∀ {x y z} → (x ∙ y) ∙ z ≃ x ∙ (y ∙ z)
      lunit : ∀ {x} → ε ∙ x ≃ x
      runit : ∀ {x} → x ∙ ε ≃ x

    cong : ∀ {x₁ y₁ x₂ y₂} → x₁ ≃ x₂ → y₁ ≃ y₂ → (x₁ ∙ y₁) ≃ (x₂ ∙ y₂)
    cong eq₁ eq₂ =
      mono (eq₁ .proj₁) (eq₂ .proj₁) ,
      mono (eq₁ .proj₂) (eq₂ .proj₂)

    interchange : (∀ {x y} → (x ∙ y) ≤ (y ∙ x)) →
                  ∀ {w x y z} → ((w ∙ x) ∙ (y ∙ z)) ≤ ((w ∙ y) ∙ (x ∙ z))
    interchange ∙-sym {w} {x} {y} {z} =
       trans (assoc .proj₁)
      (trans (mono refl (assoc .proj₂))
      (trans (mono refl (mono ∙-sym refl))
      (trans (mono refl (assoc .proj₁))
             (assoc .proj₂))))

  record IsClosure {_∙_ : A → A → A} {ε : A}
                   (∙-isMonoid : IsMonoid _∙_ ε)
                   (_-∙_ : A → A → A) : Set (a ⊔ b) where
    field
      lambda : ∀ {x y z} → (x ∙ y) ≤ z → x ≤ (y -∙ z)
      eval   : ∀ {x y} → ((x -∙ y) ∙ x) ≤ y

    open IsPreorder ≤-isPreorder
    open IsMonoid ∙-isMonoid

    -∙-mono : ∀ {x₁ y₁ x₂ y₂} → x₂ ≤ x₁ → y₁ ≤ y₂ → (x₁ -∙ y₁) ≤ (x₂ -∙ y₂)
    -∙-mono x₂≤x₁ y₁≤y₂ = lambda (trans (mono refl x₂≤x₁) (trans eval y₁≤y₂))

    lambda⁻¹ : ∀ {x y z} → x ≤ (y -∙ z) → (x ∙ y) ≤ z
    lambda⁻¹ x≤y-z = trans (mono x≤y-z refl) eval

  record IsMeet (_∧_ : A → A → A) : Set (a ⊔ b) where
    field
      π₁ : ∀ {x y} → (x ∧ y) ≤ x
      π₂ : ∀ {x y} → (x ∧ y) ≤ y
      ⟨_,_⟩ : ∀ {x y z} → x ≤ y → x ≤ z → x ≤ (y ∧ z)

    open IsPreorder ≤-isPreorder

    mono : ∀ {x₁ y₁ x₂ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ ∧ y₁) ≤ (x₂ ∧ y₂)
    mono x₁≤x₂ y₁≤y₂ = ⟨ trans π₁ x₁≤x₂ , trans π₂ y₁≤y₂ ⟩

    cong : ∀ {x₁ y₁ x₂ y₂} → x₁ ≃ x₂ → y₁ ≃ y₂ → (x₁ ∧ y₁) ≃ (x₂ ∧ y₂)
    cong m₁ m₂ = mono (m₁ .proj₁) (m₂ . proj₁) , mono (m₁ .proj₂) (m₂ . proj₂)

    assoc : ∀ {x y z} → (x ∧ y) ∧ z ≃ x ∧ (y ∧ z)
    assoc .proj₁ = ⟨ trans π₁ π₁ , ⟨ trans π₁ π₂ , π₂ ⟩ ⟩
    assoc .proj₂ = ⟨ ⟨ π₁ , trans π₂ π₁ ⟩ , trans π₂ π₂ ⟩

    idem : ∀ {x} → x ∧ x ≃ x
    idem .proj₁ = π₁
    idem .proj₂ = ⟨ refl , refl ⟩

    sym : ∀ {x y} → (x ∧ y) ≤ (y ∧ x)
    sym = ⟨ π₂ , π₁ ⟩

  record IsTop (⊤ : A) : Set (a ⊔ b) where
    field
      ≤-top : ∀ {x} → x ≤ ⊤

  record IsBigMeet iℓ (⋀ : (I : Set iℓ) → (I → A) → A) : Set (a ⊔ b ⊔ suc iℓ) where
    field
      lower    : (I : Set iℓ) (x : I → A) (i : I) → ⋀ I x ≤ x i
      greatest : (I : Set iℓ) (x : I → A) (z : A) → (∀ i → z ≤ x i) → z ≤ ⋀ I x

  module _ {_∧_ : A → A → A} {⊤ : A} (isMeet : IsMeet _∧_) (isTop : IsTop ⊤) where
    open IsPreorder ≤-isPreorder
    open IsMeet isMeet
    open IsTop isTop

    monoidOfMeet : IsMonoid _∧_ ⊤
    monoidOfMeet .IsMonoid.mono = mono
    monoidOfMeet .IsMonoid.assoc = assoc
    monoidOfMeet .IsMonoid.lunit .proj₁ = π₂
    monoidOfMeet .IsMonoid.lunit .proj₂ = ⟨ ≤-top , refl ⟩
    monoidOfMeet .IsMonoid.runit .proj₁ = π₁
    monoidOfMeet .IsMonoid.runit .proj₂ = ⟨ refl , ≤-top ⟩

  record IsJoin (_∨_ : A → A → A) : Set (a ⊔ b) where
    field
      inl : ∀ {x y} → x ≤ (x ∨ y)
      inr : ∀ {x y} → y ≤ (x ∨ y)
      [_,_] : ∀ {x y z} → x ≤ z → y ≤ z → (x ∨ y) ≤ z

    open IsPreorder ≤-isPreorder

    mono : ∀ {x₁ y₁ x₂ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ ∨ y₁) ≤ (x₂ ∨ y₂)
    mono x₁≤x₂ y₁≤y₂ = [ trans x₁≤x₂ inl , trans y₁≤y₂ inr ]

    cong : ∀ {x₁ y₁ x₂ y₂} → x₁ ≃ x₂ → y₁ ≃ y₂ → (x₁ ∨ y₁) ≃ (x₂ ∨ y₂)
    cong m₁ m₂ = mono (m₁ .proj₁) (m₂ .proj₁) , mono (m₁ .proj₂) (m₂ .proj₂)

    assoc : ∀ {x y z} → (x ∨ y) ∨ z ≃ x ∨ (y ∨ z)
    assoc .proj₁ = [ [ inl , trans inl inr ] , trans inr inr ]
    assoc .proj₂ = [ trans inl inl , [ trans inr inl , inr ] ]

    -- subsumed by sym; remove
--    comm : ∀ {x y} → x ∨ y ≃ y ∨ x
--    comm .proj₁ = [ inr , inl ]
--    comm .proj₂ = [ inr , inl ]

    idem : ∀ {x} → x ∨ x ≃ x
    idem .proj₁ = [ refl , refl ]
    idem .proj₂ = inl

    sym : ∀ {x y} → (x ∨ y) ≤ (y ∨ x)
    sym = [ inr , inl ]

  record IsBigJoin iℓ (⋁ : (I : Set iℓ) → (I → A) → A) : Set (a ⊔ b ⊔ suc iℓ) where
    field
      upper : (I : Set iℓ) (x : I → A) (i : I) → x i ≤ ⋁ I x
      least : (I : Set iℓ) (x : I → A) (z : A) → (∀ i → x i ≤ z) → ⋁ I x ≤ z

  record IsBottom (⊥ : A) : Set (a ⊔ b) where
    field
      ≤-bottom : ∀ {x} → ⊥ ≤ x

  module _ {_∨_ : A → A → A} {⊥ : A} (isJoin : IsJoin _∨_) (isBottom : IsBottom ⊥) where
    open IsPreorder ≤-isPreorder
    open IsJoin isJoin
    open IsBottom isBottom

    monoidOfJoin : IsMonoid _∨_ ⊥
    monoidOfJoin .IsMonoid.mono = mono
    monoidOfJoin .IsMonoid.assoc = assoc
    monoidOfJoin .IsMonoid.lunit .proj₁ = [ ≤-bottom , refl ]
    monoidOfJoin .IsMonoid.lunit .proj₂ = inr
    monoidOfJoin .IsMonoid.runit .proj₁ = [ refl , ≤-bottom ]
    monoidOfJoin .IsMonoid.runit .proj₂ = inl

  ------------------------------------------------------------------------------
  -- closure implies distributivity of joins and the monoid
  -- FIXME: don't assume symmetry and do the left and right ones separately
  module _ {_∙_ ε _-∙_ _∨_}
           (isMonoid : IsMonoid _∙_ ε)
           (∙-sym : ∀ {x y} → (x ∙ y) ≤ (y ∙ x))
           (isClosure : IsClosure isMonoid _-∙_)
           (isJoin : IsJoin _∨_) where
    open IsPreorder ≤-isPreorder
    open IsClosure isClosure
    open IsJoin isJoin

    ∙-∨-distrib : ∀ {x y z} → (x ∙ (y ∨ z)) ≤ ((x ∙ y) ∨ (x ∙ z))
    ∙-∨-distrib =
      trans ∙-sym (lambda⁻¹ [ lambda (trans ∙-sym inl) , lambda (trans ∙-sym inr) ])

  ------------------------------------------------------------------------------
  -- *-autonomous categories and all their structure
  record IsStarAuto {_⊗_ : A → A → A} {ε : A}
                    (⊗-isMonoid : IsMonoid _⊗_ ε)
                    (⊗-sym : ∀ {x y} → (x ⊗ y) ≤ (y ⊗ x))
                    (¬ : A → A) : Set (a ⊔ b) where
    open IsPreorder ≤-isPreorder
    field
      ¬-mono     : ∀ {x y} → x ≤ y → ¬ y ≤ ¬ x
      involution : ∀ {x} → x ≃ ¬ (¬ x)

      *-aut   : ∀ {x y z} → (x ⊗ y) ≤ ¬ z → x ≤ ¬ (y ⊗ z)
      *-aut⁻¹ : ∀ {x y z} → x ≤ ¬ (y ⊗ z) → (x ⊗ y) ≤ ¬ z

    open IsMonoid ⊗-isMonoid

    ¬-cong : ∀ {x y} → x ≃ y → ¬ x ≃ ¬ y
    ¬-cong (ϕ , ψ) .proj₁ = ¬-mono ψ
    ¬-cong (ϕ , ψ) .proj₂ = ¬-mono ϕ

    ⊥ : A
    ⊥ = ¬ ε

    _⅋_ : A → A → A
    x ⅋ y = ¬ (¬ x ⊗ ¬ y)

    ⅋-sym : ∀ {x y} → (x ⅋ y) ≤ (y ⅋ x)
    ⅋-sym = ¬-mono ⊗-sym

    ⅋-isMonoid : IsMonoid _⅋_ ⊥
    ⅋-isMonoid .IsMonoid.mono m₁ m₂ = ¬-mono (mono (¬-mono m₁) (¬-mono m₂))
    ⅋-isMonoid .IsMonoid.assoc {x}{y}{z} =
      begin
        (x ⅋ y) ⅋ z            ≡⟨⟩
        ¬ (¬ (x ⅋ y) ⊗ ¬ z)     ≈˘⟨ ¬-cong (cong involution (refl , refl)) ⟩
        ¬ ((¬ x ⊗ ¬ y) ⊗ ¬ z)   ≈⟨ ¬-cong assoc ⟩
        ¬ (¬ x ⊗ (¬ y ⊗ ¬ z))   ≈⟨ ¬-cong (cong (refl , refl) involution) ⟩
        ¬ (¬ x ⊗ ¬ (y ⅋ z))     ≡⟨⟩
        x ⅋ (y ⅋ z)            ∎
      where open import Relation.Binary.Reasoning.Setoid setoidOf
    ⅋-isMonoid .IsMonoid.lunit {x} =
      begin
        ⊥ ⅋ x             ≡⟨⟩
        ¬ (¬ (¬ ε) ⊗ ¬ x)  ≈˘⟨ ¬-cong (cong involution (refl , refl)) ⟩
        ¬ (ε ⊗ ¬ x)        ≈⟨ ¬-cong lunit ⟩
        ¬ (¬ x)            ≈˘⟨ involution ⟩
        x                  ∎
      where open import Relation.Binary.Reasoning.Setoid setoidOf
    ⅋-isMonoid .IsMonoid.runit {x} =
      begin
        x ⅋ ⊥             ≡⟨⟩
        ¬ (¬ x ⊗ ¬ (¬ ε))  ≈˘⟨ ¬-cong (cong (refl , refl) involution) ⟩
        ¬ (¬ x ⊗ ε)        ≈⟨ ¬-cong runit ⟩
        ¬ (¬ x)            ≈˘⟨ involution ⟩
        x                  ∎
      where open import Relation.Binary.Reasoning.Setoid setoidOf

    open IsMonoid ⅋-isMonoid
      renaming (mono to ⅋-mono;
                cong to ⅋-cong;
                assoc to ⅋-assoc;
                lunit to ⅋-lunit;
                runit to ⅋-runit) public

    ev : ∀ {x} → (x ⊗ ¬ x) ≤ ⊥
    ev = *-aut⁻¹ (trans (involution .proj₁) (¬-mono (runit .proj₁)))

    _⊸_ : A → A → A
    x ⊸ y = ¬ x ⅋ y

    ⊸-isClosure : IsClosure ⊗-isMonoid _⊸_
    ⊸-isClosure .IsClosure.lambda m =
      *-aut (trans (mono refl (involution .proj₂)) (trans m (involution .proj₁)))
    ⊸-isClosure .IsClosure.eval =
      trans (*-aut⁻¹ (¬-mono (mono (involution .proj₁) refl))) (involution .proj₂)

    coev : ∀ {x} → ε ≤ (x ⅋ ¬ x)
    coev = trans (⊸-isClosure .IsClosure.lambda (lunit .proj₁)) ⅋-sym

    linear-distrib : ∀ {x y z} → (x ⊗ (y ⅋ z)) ≤ ((x ⊗ y) ⅋ z)
    linear-distrib =
      trans (*-aut (trans (assoc .proj₁)
                   (trans (mono refl (trans (mono (trans (⅋-mono refl (involution .proj₁)) ⅋-sym) refl) (⊸-isClosure .IsClosure.eval)))
                          (involution .proj₁))))
            ⅋-sym

  ------------------------------------------------------------------------------
  record IsClosureOp (C : A → A) : Set (a ⊔ b) where
    open IsPreorder ≤-isPreorder

    field
      mono   : ∀ {x y} → x ≤ y → C x ≤ C y
      unit   : ∀ {x} → x ≤ C x
      closed : ∀ {x} → C (C x) ≤ C x

    idem : ∀ {x} → C (C x) ≃ C x
    idem .proj₁ = closed
    idem .proj₂ = mono unit

  ------------------------------------------------------------------------------
  record IsDuoidal {_⊗_ : A → A → A} {ε : A} {_⍮_ : A → A → A} {ι : A}
                   (⊗-isMonoid : IsMonoid _⊗_ ε)
                   (⍮-isMonoid : IsMonoid _⍮_ ι) : Set (a ⊔ b) where
    field
      exchange : ∀ {w x y z} → ((w ⍮ x) ⊗ (y ⍮ z)) ≤ ((w ⊗ y) ⍮ (x ⊗ z))
      mu       : (ι ⊗ ι) ≤ ι
      -- (Δ : ε ≤ (ε ▷ ε)) -- what is this needed for?
      -- (u : ε ≤ ι) -- what is this needed for?
