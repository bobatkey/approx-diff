{-# OPTIONS --postfix-projections --safe --prop #-}

module basics where

open import Level using (_⊔_; suc)
open import prop renaming (⊥ to ⊥p)
open import prop-setoid using (IsEquivalence; Setoid; module ≈-Reasoning)

module _ {a} {A : Set a} where

  Op : ∀ {b} → (A → A → Prop b) → (A → A → Prop b)
  Op R x y = R y x

  SymmetricCore : ∀ {b} → (A → A → Prop b) → (A → A → Prop b)
  SymmetricCore R x y = R x y ∧ R y x

  record IsPreorder {b} (_≤_ : A → A → Prop b) : Prop (a ⊔ b) where
    field
      refl  : ∀ {x} → x ≤ x
      trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

    -- Derived equivalence relation
    _≃_ = SymmetricCore _≤_

    ≃-refl : ∀ {x} → x ≃ x
    ≃-refl = refl , refl

    ≃-sym : ∀ {x y} → x ≃ y → y ≃ x
    ≃-sym (x≤y , y≤x) = y≤x , x≤y

    ≃-trans : ∀ {x y z} → x ≃ y → y ≃ z → x ≃ z
    ≃-trans (x≤y , y≤x) (y≤z , z≤y) =
      (trans x≤y y≤z) , (trans z≤y y≤x)

    isEquivalence : IsEquivalence _≃_
    isEquivalence .IsEquivalence.refl = ≃-refl
    isEquivalence .IsEquivalence.sym = ≃-sym
    isEquivalence .IsEquivalence.trans = ≃-trans

    infix 4 _≃_

    -- The opposite order
    opposite : IsPreorder (Op _≤_)
    opposite .refl = refl
    opposite .trans y≤x z≤y = trans z≤y y≤x

module ≤-Reasoning {o i} {A : Set o} {_≤_ : A → A → Prop i} (isPreorder : IsPreorder _≤_) where
  open IsPreorder

  infix  1 begin_
  infixr 2 _≤⟨_⟩_ _≡⟨⟩_
  infix  4 _∎

  begin_ : ∀ {x y : A}
    → x ≤ y
      -----
    → x ≤ y
  begin x≤y  =  x≤y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≤ y
      -----
    → x ≤ y
  x ≡⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≤ y
    → y ≤ z
      -----
    → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z  =  isPreorder .trans x≤y y≤z

  _∎ : ∀ (x : A)
      -----
    → x ≤ x
  x ∎  =  isPreorder .refl


module _ {a b} {A : Set a} {_≤_ : A → A → Prop b} (≤-isPreorder : IsPreorder _≤_) where

  open IsPreorder ≤-isPreorder

  setoidOf : Setoid a b
  setoidOf .Setoid.Carrier = A
  setoidOf .Setoid._≈_ = SymmetricCore _≤_
  setoidOf .Setoid.isEquivalence = isEquivalence

  record IsMonoid (_∙_ : A → A → A) (ε : A) : Set (a ⊔ b) where
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
                  ∀ {w x y z} → ((w ∙ x) ∙ (y ∙ z)) ≃ ((w ∙ y) ∙ (x ∙ z))
    interchange sym {w} {x} {y} {z} =
      begin
        (w ∙ x) ∙ (y ∙ z)
      ≈⟨ assoc ⟩
        w ∙ (x ∙ (y ∙ z))
      ≈˘⟨ cong ≃-refl assoc ⟩
        w ∙ ((x ∙ y) ∙ z)
      ≈⟨ cong ≃-refl (cong (sym , sym) ≃-refl) ⟩
        w ∙ ((y ∙ x) ∙ z)
      ≈⟨ cong ≃-refl assoc ⟩
        w ∙ (y ∙ (x ∙ z))
      ≈˘⟨ assoc ⟩
        (w ∙ y) ∙ (x ∙ z)
      ∎ where open ≈-Reasoning isEquivalence

  record IsResidual {_∙_ : A → A → A} {ε : A}
                    (∙-isMonoid : IsMonoid _∙_ ε)
                    (_-∙_ : A → A → A) : Set (a ⊔ b) where
    field
      lambda : ∀ {x y z} → (x ∙ y) ≤ z → x ≤ (y -∙ z)
      eval   : ∀ {x y} → ((x -∙ y) ∙ x) ≤ y

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

    comm : ∀ {x y} → (x ∧ y) ≤ (y ∧ x)
    comm = ⟨ π₂ , π₁ ⟩

  record IsTop (⊤ : A) : Set (a ⊔ b) where
    field
      ≤-top : ∀ {x} → x ≤ ⊤

  record IsBigMeet iℓ (⋀ : (I : Set iℓ) → (I → A) → A) : Set (a ⊔ b ⊔ suc iℓ) where
    field
      lower    : (I : Set iℓ) (x : I → A) (i : I) → ⋀ I x ≤ x i
      greatest : (I : Set iℓ) (x : I → A) (z : A) → (∀ i → z ≤ x i) → z ≤ ⋀ I x

  module _ {_∧_ : A → A → A} {⊤ : A} (isMeet : IsMeet _∧_) (isTop : IsTop ⊤) where
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

    mono : ∀ {x₁ y₁ x₂ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ ∨ y₁) ≤ (x₂ ∨ y₂)
    mono x₁≤x₂ y₁≤y₂ = [ trans x₁≤x₂ inl , trans y₁≤y₂ inr ]

    cong : ∀ {x₁ y₁ x₂ y₂} → x₁ ≃ x₂ → y₁ ≃ y₂ → (x₁ ∨ y₁) ≃ (x₂ ∨ y₂)
    cong m₁ m₂ = mono (m₁ .proj₁) (m₂ .proj₁) , mono (m₁ .proj₂) (m₂ .proj₂)

    assoc : ∀ {x y z} → (x ∨ y) ∨ z ≃ x ∨ (y ∨ z)
    assoc .proj₁ = [ [ inl , trans inl inr ] , trans inr inr ]
    assoc .proj₂ = [ trans inl inl , [ trans inr inl , inr ] ]

    idem : ∀ {x} → x ∨ x ≃ x
    idem .proj₁ = [ refl , refl ]
    idem .proj₂ = inl

    comm : ∀ {x y} → (x ∨ y) ≤ (y ∨ x)
    comm = [ inr , inl ]

  record IsBigJoin iℓ (⋁ : (I : Set iℓ) → (I → A) → A) : Set (a ⊔ b ⊔ suc iℓ) where
    field
      upper : (I : Set iℓ) (x : I → A) (i : I) → x i ≤ ⋁ I x
      least : (I : Set iℓ) (x : I → A) (z : A) → (∀ i → x i ≤ z) → ⋁ I x ≤ z

    mono : {I : Set iℓ} {x y : I → A} → (∀ i → x i ≤ y i) → ⋁ I x ≤ ⋁ I y
    mono f = least _ _ _ (λ i → trans (f i) (upper _ _ i))

  record IsBottom (⊥ : A) : Set (a ⊔ b) where
    field
      ≤-bottom : ∀ {x} → ⊥ ≤ x

  module _ {_∨_ : A → A → A} {⊥ : A} (isJoin : IsJoin _∨_) (isBottom : IsBottom ⊥) where
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
  -- residual implies distributivity of joins and the monoid
  -- FIXME: don't assume symmetry and do the left and right ones separately
  module _ {_∙_ ε _-∙_ _∨_}
           (isMonoid : IsMonoid _∙_ ε)
           (∙-sym : ∀ {x y} → (x ∙ y) ≤ (y ∙ x))
           (isResidual : IsResidual isMonoid _-∙_)
           (isJoin : IsJoin _∨_) where
    open IsResidual isResidual
    open IsJoin isJoin

    ∙-∨-distrib : ∀ {x y z} → (x ∙ (y ∨ z)) ≤ ((x ∙ y) ∨ (x ∙ z))
    ∙-∨-distrib =
      trans ∙-sym (lambda⁻¹ [ lambda (trans ∙-sym inl) , lambda (trans ∙-sym inr) ])

  ------------------------------------------------------------------------------
  -- *-autonomous categories and all their structure
  --
  -- Barr, Michael. *-Autonomous Categories. Vol. 752. Lecture Notes
  -- in Mathematics. Berlin, Heidelberg: Springer,
  -- 1979. https://doi.org/10.1007/BFb0064579.
  record IsStarAuto {_⊗_ : A → A → A} {ε : A}
                    (⊗-isMonoid : IsMonoid _⊗_ ε)
                    (⊗-sym : ∀ {x y} → (x ⊗ y) ≤ (y ⊗ x))
                    (¬ : A → A) : Set (a ⊔ b) where
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
      where open ≈-Reasoning isEquivalence
    ⅋-isMonoid .IsMonoid.lunit {x} =
      begin
        ⊥ ⅋ x             ≡⟨⟩
        ¬ (¬ (¬ ε) ⊗ ¬ x)  ≈˘⟨ ¬-cong (cong involution (refl , refl)) ⟩
        ¬ (ε ⊗ ¬ x)        ≈⟨ ¬-cong lunit ⟩
        ¬ (¬ x)            ≈˘⟨ involution ⟩
        x                  ∎
      where open ≈-Reasoning isEquivalence
    ⅋-isMonoid .IsMonoid.runit {x} =
      begin
        x ⅋ ⊥             ≡⟨⟩
        ¬ (¬ x ⊗ ¬ (¬ ε))  ≈˘⟨ ¬-cong (cong (refl , refl) involution) ⟩
        ¬ (¬ x ⊗ ε)        ≈⟨ ¬-cong runit ⟩
        ¬ (¬ x)            ≈˘⟨ involution ⟩
        x                  ∎
      where open ≈-Reasoning isEquivalence

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

    ⊸-isResidual : IsResidual ⊗-isMonoid _⊸_
    ⊸-isResidual .IsResidual.lambda m =
      *-aut (trans (mono refl (involution .proj₂)) (trans m (involution .proj₁)))
    ⊸-isResidual .IsResidual.eval =
      trans (*-aut⁻¹ (¬-mono (mono (involution .proj₁) refl))) (involution .proj₂)

    coev : ∀ {x} → ε ≤ (x ⅋ ¬ x)
    coev = trans (⊸-isResidual .IsResidual.lambda (lunit .proj₁)) ⅋-sym

    linear-distrib : ∀ {x y z} → (x ⊗ (y ⅋ z)) ≤ ((x ⊗ y) ⅋ z)
    linear-distrib {x} {y} {z} =
      begin
        x ⊗ (y ⅋ z)
      ≤⟨ *-aut (begin
                 (x ⊗ (y ⅋ z)) ⊗ ¬ z        ≤⟨ assoc .proj₁ ⟩
                 x ⊗ ((y ⅋ z) ⊗ ¬ z)        ≤⟨ mono refl (mono (⅋-mono refl (involution .proj₁)) refl) ⟩
                 x ⊗ ((y ⅋ ¬ (¬ z)) ⊗ ¬ z)  ≤⟨ mono refl (mono ⅋-sym refl) ⟩
                 x ⊗ ((¬ (¬ z) ⅋ y) ⊗ ¬ z)  ≤⟨ mono refl (⊸-isResidual .IsResidual.eval) ⟩
                 x ⊗ y                       ≤⟨ involution .proj₁ ⟩
                 ¬ (¬ (x ⊗ y))              ∎) ⟩
        z ⅋ (x ⊗ y)
      ≤⟨ ⅋-sym ⟩
        (x ⊗ y) ⅋ z
      ∎
      where open ≤-Reasoning ≤-isPreorder

  ------------------------------------------------------------------------------
  record IsClosureOp (C : A → A) : Set (a ⊔ b) where

    field
      mono   : ∀ {x y} → x ≤ y → C x ≤ C y
      unit   : ∀ {x} → x ≤ C x
      closed : ∀ {x} → C (C x) ≤ C x

    idem : ∀ {x} → C (C x) ≃ C x
    idem .proj₁ = closed
    idem .proj₂ = mono unit

  ------------------------------------------------------------------------------
  record IsDuoidal (_⊗_ : A → A → A) (ε : A) (_⍮_ : A → A → A) (ι : A) : Set (a ⊔ b) where
    field
      exchange : ∀ {w x y z} → ((w ⍮ x) ⊗ (y ⍮ z)) ≤ ((w ⊗ y) ⍮ (x ⊗ z))
      mu       : (ι ⊗ ι) ≤ ι
      nu       : ε ≤ (ε ⍮ ε)
      gu       : ε ≤ ι

  -- If a monoid is commutative, then it is duoidal over itself
  module _ {_∙_ : A → A → A} {ε : A} (∙-isMonoid : IsMonoid _∙_ ε)
           (∙-comm : ∀ {x y} → (x ∙ y) ≤ (y ∙ x)) where

    open IsMonoid ∙-isMonoid

    selfDuoidal : IsDuoidal _∙_ ε _∙_ ε
    selfDuoidal .IsDuoidal.exchange = interchange ∙-comm .proj₁
    selfDuoidal .IsDuoidal.mu = lunit .proj₁
    selfDuoidal .IsDuoidal.nu = lunit .proj₂
    selfDuoidal .IsDuoidal.gu = refl

  -- FIXME: duoidal is automatic over/under meets/joins
