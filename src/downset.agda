{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level
  using (suc; Lift; lift; lower)
  renaming (_⊔_ to _⊔ℓ_)
open import prop
  using (LiftP; lift; lower; tt; _∨_; _∧_; inj₁; inj₂; _,_; proj₁; proj₂; ∃)
  renaming (⊥ to ⊥p; ⊤ to ⊤p)
open import basics
  using (IsPreorder; module ≤-Reasoning;
         IsBottom; IsTop; IsMeet; IsJoin;
         IsBigMeet; IsBigJoin;
         IsMonoid; monoidOfJoin; monoidOfMeet;
         IsResidual; IsDuoidal)

module downset {aℓ bℓ} cℓ
  {A : Set aℓ} {_≤_ : A → A → Prop bℓ} (≤-isPreorder : IsPreorder _≤_)
  where

open IsPreorder ≤-isPreorder
  renaming ( refl to ≤-refl
           ; trans to ≤-trans
           ; _≃_ to _≈_
           ; isEquivalence to ≈-isEquivalence )

record Elt : Set (suc aℓ ⊔ℓ suc bℓ ⊔ℓ suc cℓ) where
  no-eta-equality
  field
    Carrier  : A → Prop (aℓ ⊔ℓ bℓ ⊔ℓ cℓ)
    ≤-closed : ∀ {a b} → a ≤ b → Carrier b → Carrier a
open Elt

record _⊑_ (X Y : Elt) : Prop (aℓ ⊔ℓ bℓ ⊔ℓ cℓ) where
  no-eta-equality
  field
    *≤* : ∀ {a} → X .Carrier a → Y .Carrier a
open _⊑_

⊑-isPreorder : IsPreorder _⊑_
⊑-isPreorder .IsPreorder.refl .*≤* a∈X = a∈X
⊑-isPreorder .IsPreorder.trans X⊑Y Y⊑Z .*≤* a∈X = Y⊑Z .*≤* (X⊑Y .*≤* a∈X)

open IsPreorder ⊑-isPreorder
  renaming (isEquivalence to ≃-isEquivalence)

------------------------------------------------------------------------------
-- Embedding of A via principal downsets

η : A → Elt
η x .Carrier a = LiftP (aℓ ⊔ℓ cℓ) (a ≤ x)
η x .≤-closed a≤b (lift b≤x) = lift (≤-trans a≤b b≤x)

η-mono : ∀ {x y} → x ≤ y → η x ⊑ η y
η-mono x≤y .*≤* (lift a≤x) .lower = ≤-trans a≤x x≤y

η-reflect : ∀ {x y} → η x ⊑ η y → x ≤ y
η-reflect ηx⊑ηy = ηx⊑ηy .*≤* (lift ≤-refl) .lower

------------------------------------------------------------------------------
-- Lattice structure

--------
-- Meets

⊤ : Elt
⊤ .Carrier a = ⊤p
⊤ .≤-closed _ tt = tt

⊤-isTop : IsTop ⊑-isPreorder ⊤
⊤-isTop .IsTop.≤-top .*≤* x = tt

_⊔_ : Elt → Elt → Elt
(X ⊔ Y) .Carrier a = X .Carrier a ∨ Y .Carrier a
(X ⊔ Y) .≤-closed a≤b (inj₁ b∈X) = inj₁ (X .≤-closed a≤b b∈X)
(X ⊔ Y) .≤-closed a≤b (inj₂ b∈Y) = inj₂ (Y .≤-closed a≤b b∈Y)

_⊓_ : Elt → Elt → Elt
(X ⊓ Y) .Carrier a = X .Carrier a ∧ Y .Carrier a
(X ⊓ Y) .≤-closed a≤b (a∈X , a∈Y) = X .≤-closed a≤b a∈X , Y .≤-closed a≤b a∈Y

⊓-isMeet : IsMeet ⊑-isPreorder _⊓_
⊓-isMeet .IsMeet.π₁ .*≤* = proj₁
⊓-isMeet .IsMeet.π₂ .*≤* = proj₂
⊓-isMeet .IsMeet.⟨_,_⟩ X⊑Y X⊑Z .*≤* a∈X = X⊑Y .*≤* a∈X , X⊑Z .*≤* a∈X

open IsMeet ⊓-isMeet
  renaming ( comm to ⊓-comm
           ; mono to ⊓-mono
           ; assoc to ⊓-assoc
           ; cong to ⊓-cong
           ; idem to ⊓-idem)
  public

-- FIXME: η preserves meets that exist in A

⊓-isMonoid : IsMonoid ⊑-isPreorder _⊓_ ⊤
⊓-isMonoid = monoidOfMeet ⊑-isPreorder ⊓-isMeet ⊤-isTop

--------
-- Joins

⊥ : Elt
⊥ .Carrier a = ⊥p

⊥-isBottom : IsBottom ⊑-isPreorder ⊥
⊥-isBottom .IsBottom.≤-bottom .*≤* ()

⊔-isJoin : IsJoin ⊑-isPreorder _⊔_
⊔-isJoin .IsJoin.inl .*≤* = inj₁
⊔-isJoin .IsJoin.inr .*≤* = inj₂
⊔-isJoin .IsJoin.[_,_] X⊑Z Y⊑Z .*≤* (inj₁ a∈X) = X⊑Z .*≤* a∈X
⊔-isJoin .IsJoin.[_,_] X⊑Z Y⊑Z .*≤* (inj₂ a∈Y) = Y⊑Z .*≤* a∈Y

⊔-isMonoid : IsMonoid ⊑-isPreorder _⊔_ ⊥
⊔-isMonoid = monoidOfJoin ⊑-isPreorder ⊔-isJoin ⊥-isBottom

----------------------------
-- Distributivity properties

⊓-⊔-distrib : ∀ {X Y Z} → (X ⊓ (Y ⊔ Z)) ≃ ((X ⊓ Y) ⊔ (X ⊓ Z))
⊓-⊔-distrib .proj₁ .*≤* (a∈X , inj₁ a∈Y) = inj₁ (a∈X , a∈Y)
⊓-⊔-distrib .proj₁ .*≤* (a∈X , inj₂ a∈Z) = inj₂ (a∈X , a∈Z)
⊓-⊔-distrib .proj₂ .*≤* (inj₁ (a∈X , a∈Y)) = a∈X , inj₁ a∈Y
⊓-⊔-distrib .proj₂ .*≤* (inj₂ (a∈X , a∈Z)) = a∈X , inj₂ a∈Z

⊓-⊥-distrib : ∀ {X} → (X ⊓ ⊥) ≃ ⊥
⊓-⊥-distrib .proj₁ .*≤* ()
⊓-⊥-distrib .proj₂ .*≤* ()

⊔-⊓-distrib : ∀ {X Y Z} → (X ⊔ (Y ⊓ Z)) ≃ ((X ⊔ Y) ⊓ (X ⊔ Z))
⊔-⊓-distrib .proj₁ .*≤* (inj₁ a∈X) = inj₁ a∈X , inj₁ a∈X
⊔-⊓-distrib .proj₁ .*≤* (inj₂ (a∈Y , a∈Z)) = inj₂ a∈Y , inj₂ a∈Z
⊔-⊓-distrib .proj₂ .*≤* (inj₁ a∈X , _) = inj₁ a∈X
⊔-⊓-distrib .proj₂ .*≤* (inj₂ a∈Y , inj₁ a∈X) = inj₁ a∈X
⊔-⊓-distrib .proj₂ .*≤* (inj₂ a∈Y , inj₂ a∈Z) = inj₂ (a∈Y , a∈Z)

⊔-⊤-distrib : ∀ {X} → (X ⊔ ⊤) ≃ ⊤
⊔-⊤-distrib .proj₁ .*≤* x = tt
⊔-⊤-distrib .proj₂ .*≤* = inj₂

-------------------
-- Residual for _⊓_

_⇒_ : Elt → Elt → Elt
(X ⇒ Y) .Carrier a = ∀ c → c ≤ a → X .Carrier c → Y .Carrier c
(X ⇒ Y) .≤-closed a≤b f c c≤a c∈X = f c (≤-trans c≤a a≤b) c∈X

⇒-isResidual : IsResidual ⊑-isPreorder ⊓-isMonoid _⇒_
⇒-isResidual .IsResidual.lambda {X} {Y} {Z} f .*≤* a∈X c c≤a c∈Y =
  f .*≤* (X .≤-closed c≤a a∈X , c∈Y)
⇒-isResidual .IsResidual.eval .*≤* (f , a∈X) = f _ ≤-refl a∈X

------------------------------------------------------------------------------
-- Infinitary meets and joins

⋂ : (I : Set cℓ) → (I → Elt) → Elt
⋂ I X .Carrier a = ∀ i → X i .Carrier a
⋂ I X .≤-closed a≤b x i = X i .≤-closed a≤b (x i)

⋂-isBigMeet : IsBigMeet ⊑-isPreorder cℓ ⋂
⋂-isBigMeet .IsBigMeet.lower I X i .*≤* x = x i
⋂-isBigMeet .IsBigMeet.greatest I f Z X .*≤* a∈Z i = X i .*≤* a∈Z

⋃ : (I : Set cℓ) → (I → Elt) → Elt
⋃ I X .Carrier a = ∃ I λ i → X i .Carrier a
⋃ I X .≤-closed a≤b (i , x) = i , X i .≤-closed a≤b x

⋃-isBigJoin : IsBigJoin ⊑-isPreorder cℓ ⋃
⋃-isBigJoin .IsBigJoin.upper I X i .*≤* a∈Xi = i , a∈Xi
⋃-isBigJoin .IsBigJoin.least I X Z f .*≤* (i , a∈Xi) = f i .*≤* a∈Xi

open IsBigJoin ⋃-isBigJoin
  renaming (mono to ⋃-mono)

-- FIXME: distributivity properties

------------------------------------------------------------------------------
-- Day monoids
module Day {_∙_ ε} (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ε) where

  open IsMonoid ∙-isMonoid
    renaming (mono to ∙-mono; assoc to ∙-assoc; lunit to ∙-lunit; runit to ∙-runit)

  _⊗_ : Elt → Elt → Elt
  (X ⊗ Y) .Carrier a = ∃ A λ a₁ → ∃ A λ a₂ → (a ≤ (a₁ ∙ a₂)) ∧ (X .Carrier a₁ ∧ Y .Carrier a₂)
  (X ⊗ Y) .≤-closed a≤b (a₁ , a₂ , b≤a₁a₂ , a₁∈X , a₂∈Y) =
    a₁ , a₂ , ≤-trans a≤b b≤a₁a₂ , a₁∈X , a₂∈Y

  I : Elt
  I = η ε

  ⊗-isMonoid : IsMonoid ⊑-isPreorder _⊗_ I
  ⊗-isMonoid .IsMonoid.mono X₁⊑X₂ Y₁⊑Y₂ .*≤* (a₁ , a₂ , a≤a₁a₂ , a₁∈X₁ , a₂∈Y₁) =
    a₁ , a₂ , a≤a₁a₂ , X₁⊑X₂ .*≤* a₁∈X₁ , Y₁⊑Y₂ .*≤* a₂∈Y₁
  ⊗-isMonoid .IsMonoid.assoc .proj₁ .*≤* (a₁ , a₂ , a≤a₁a₂ , (a₃ , a₄ , a₁≤a₃a₄ , a₃∈X , a₄∈Y) , a₂∈Z) =
    a₃ , a₄ ∙ a₂ ,
    ≤-trans a≤a₁a₂ (≤-trans (∙-mono a₁≤a₃a₄ ≤-refl) (∙-assoc .proj₁)) ,
    a₃∈X ,
    a₄ , a₂ , ≤-refl , a₄∈Y , a₂∈Z
  ⊗-isMonoid .IsMonoid.assoc .proj₂ .*≤* (a₁ , a₂ , a≤a₁a₂ , a₁∈X , a₃ , a₄ , a₂≤a₃a₄ , a₃∈Y , a₄∈Z) =
    a₁ ∙ a₃ , a₄ , ≤-trans a≤a₁a₂ (≤-trans (∙-mono ≤-refl a₂≤a₃a₄) (∙-assoc .proj₂)) ,
    (a₁ , a₃ , ≤-refl , a₁∈X , a₃∈Y) ,
    a₄∈Z
  ⊗-isMonoid .IsMonoid.lunit {X} .proj₁ .*≤* (a₁ , a₂ , a≤a₁a₂ , lift a₁≤ε , a₂∈X) = X .≤-closed (≤-trans a≤a₁a₂ (≤-trans (∙-mono a₁≤ε ≤-refl) (∙-lunit .proj₁))) a₂∈X
  ⊗-isMonoid .IsMonoid.lunit {X} .proj₂ .*≤* {a} a∈X = ε , a , ∙-lunit .proj₂ , lift ≤-refl , a∈X
  ⊗-isMonoid .IsMonoid.runit {X} .proj₁ .*≤* (a₁ , a₂ , a≤a₁a₂ , a₁∈X , lift a₂≤ε) = X .≤-closed (≤-trans a≤a₁a₂ (≤-trans (∙-mono ≤-refl a₂≤ε) (∙-runit .proj₁))) a₁∈X
  ⊗-isMonoid .IsMonoid.runit {X} .proj₂ .*≤* {a} a∈X = a , ε , ∙-runit .proj₂ , a∈X , lift ≤-refl

  η-preserve-∙ : ∀ {x y} → η (x ∙ y) ≃ (η x ⊗ η y)
  η-preserve-∙ {x} {y} .proj₁ .*≤* {a} (lift a≤xy) =
    x , y , a≤xy , lift ≤-refl , lift ≤-refl
  η-preserve-∙ {x} {y} .proj₂ .*≤* {a} (a₁ , a₂ , a≤a₁a₂ , lift a₁≤x , lift a₂≤y) =
    lift (≤-trans a≤a₁a₂ (∙-mono a₁≤x a₂≤y))

  -- Distributivity wrt joins
  ⊗-⋃-distribₗ : ∀ {I X Y} → (⋃ I X ⊗ Y) ≃ ⋃ I (λ i → X i ⊗ Y)
  ⊗-⋃-distribₗ .proj₁ .*≤* (a₁ , a₂ , a≤a₁a₂ , (i , a₁∈Xi) , a₂∈Y) = i , a₁ , a₂ , a≤a₁a₂ , a₁∈Xi , a₂∈Y
  ⊗-⋃-distribₗ .proj₂ .*≤* (i , a₁ , a₂ , a≤a₁a₂ , a₁∈Xi , a₂∈Y)   = a₁ , a₂ , a≤a₁a₂ , (i , a₁∈Xi) , a₂∈Y

  ⊗-⋃-distribᵣ : ∀ {I X Y} → (X ⊗ ⋃ I Y) ≃ ⋃ I (λ i → X ⊗ Y i)
  ⊗-⋃-distribᵣ .proj₁ .*≤* (a₁ , a₂ , a≤a₁a₂ , a₁∈X , (i , a₂∈Yi)) = i , a₁ , a₂ , a≤a₁a₂ , a₁∈X , a₂∈Yi
  ⊗-⋃-distribᵣ .proj₂ .*≤* (i , a₁ , a₂ , a≤a₁a₂ , a₁∈X , a₂∈Yi)   = a₁ , a₂ , a≤a₁a₂ , a₁∈X , (i , a₂∈Yi)

  -- Left residual
  _>->_ : Elt → Elt → Elt
  (X >-> Y) .Carrier a = ∀ c → X .Carrier c → Y .Carrier (a ∙ c)
  (X >-> Y) .≤-closed a≤b f c c∈X = Y .≤-closed (∙-mono a≤b ≤-refl) (f c c∈X)

  -- Right residual
  _->>_ : Elt → Elt → Elt
  (X ->> Y) .Carrier a = ∀ c → X .Carrier c → Y .Carrier (c ∙ a)
  (X ->> Y) .≤-closed a≤b f c c∈X = Y .≤-closed (∙-mono ≤-refl a≤b) (f c c∈X)

  -- FIXME: prove that these are left/right residuals.

  -- FIXME: η preserves residuals that already exist.

------------------------------------------------------------------------------
-- Commutative Day Monoids
module CommutativeDay {_∙_ ε}
         (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ε)
         (∙-comm : ∀ {x y} → (x ∙ y) ≤ (y ∙ x)) where

  open IsMonoid ∙-isMonoid
    renaming (mono to ∙-mono; assoc to ∙-assoc; lunit to ∙-lunit; runit to ∙-runit)

  open Day ∙-isMonoid public
    -- FIXME: think about what to export here

  ⊗-comm : ∀ {X Y} → (X ⊗ Y) ⊑ (Y ⊗ X)
  ⊗-comm .*≤* (a₁ , a₂ , a≤a₁a₂ , a₁∈X , a₂∈Y) =
    a₂ , a₁ , ≤-trans a≤a₁a₂ ∙-comm , a₂∈Y , a₁∈X

  -- FIXME: prove that the left and right residuals above are equal,
  -- and give the residuals a single name here.
  _⊸_ : Elt → Elt → Elt
  (X ⊸ Y) .Carrier a = ∀ c → X .Carrier c → Y .Carrier (a ∙ c)
  (X ⊸ Y) .≤-closed a≤b f c c∈X = Y .≤-closed (∙-mono a≤b ≤-refl) (f c c∈X)

  ⊸-isResidual : IsResidual ⊑-isPreorder ⊗-isMonoid _⊸_
  ⊸-isResidual .IsResidual.lambda f .*≤* a∈X c c∈Y =
    f .*≤* (_ , c , ≤-refl , a∈X , c∈Y)
  ⊸-isResidual .IsResidual.eval {X} {Y} .*≤* (a₁ , a₂ , a≤a₁a₂ , f , a₂∈X) =
    Y .≤-closed a≤a₁a₂ (f a₂ a₂∈X)

  -- FIXME: if _∙_ has a residual, then η preserves it

  -- FIXME: ！-exponentials from A, as well.
  module FreeExponential where
    ！ : Elt → Elt
    ！ X .Carrier a = ∃ A λ c → (a ≤ c) ∧ ((c ≤ ε) ∧ ((c ≤ (c ∙ c)) ∧ X .Carrier c))
    ！ X .≤-closed a≤b (c , b≤c , c≤ε , c≤cc , c∈X) =
        c , ≤-trans a≤b b≤c , c≤ε , c≤cc , c∈X

    ！-mono : ∀ {X Y} → X ⊑ Y → ！ X ⊑ ！ Y
    ！-mono X⊑Y .*≤* (c , a≤c , c≤ε , c≤cc , c∈X) =
       c , a≤c , c≤ε , c≤cc , X⊑Y .*≤* c∈X

    ！-monoidal : ∀ {X Y} → (！ X ⊗ ！ Y) ⊑ ！ (X ⊗ Y)
    ！-monoidal .*≤* (a₁ , a₂ , a≤a₁a₂ , (c₁ , a₁≤c₁ , c₁≤ε , c₁≤c₁c₁ , c₁∈X) ,
                                         (c₂ , a₂≤c₂ , c₂≤ε , c₂≤c₂c₂ , c₂∈Y)) =
        c₁ ∙ c₂ , ≤-trans a≤a₁a₂ (∙-mono a₁≤c₁ a₂≤c₂) ,
        ≤-trans (∙-mono c₁≤ε c₂≤ε) (∙-lunit .proj₁) ,
        ≤-trans (∙-mono c₁≤c₁c₁ c₂≤c₂c₂) (interchange ∙-comm .proj₁) ,
        c₁ , c₂ , ≤-refl , c₁∈X , c₂∈Y

    ！-discard : ∀ {X} → ！ X ⊑ I
    ！-discard .*≤* (c , a≤c , c≤ε , _ , _) = lift (≤-trans a≤c c≤ε)

    ！-duplicate : ∀ {X} → ！ X ⊑ (！ X ⊗ ！ X)
    ！-duplicate .*≤* (c , a≤c , c≤ε , c≤cc , c∈X) =
      c , c , ≤-trans a≤c c≤cc ,
      (c , ≤-refl , c≤ε , c≤cc , c∈X) ,
      (c , ≤-refl , c≤ε , c≤cc , c∈X)

    ！-derelict : ∀ {X} → ！ X ⊑ X
    ！-derelict {X} .*≤* (c , a≤c , c≤ε , c≤cc , c∈X) = X .≤-closed a≤c c∈X

    ！-dig : ∀ {X} → ！ X ⊑ ！ (！ X)
    ！-dig .*≤* (c , a≤c , c≤ε , c≤cc , c∈X) =
      c , a≤c , c≤ε , c≤cc , (c , ≤-refl , c≤ε , c≤cc , c∈X)

    -- Embeddings of “comonoids” are closed under ！
    η-preserve-！ : ∀ {x} → x ≤ ε → x ≤ (x ∙ x) → η x ≃ ！ (η x)
    η-preserve-！ {x} x≤ε x≤xx .proj₁ .*≤* (lift a≤x) =
      x , a≤x , x≤ε , x≤xx , lift ≤-refl
    η-preserve-！ {x} x≤ε x≤xx .proj₂ .*≤* (c , a≤c , _ , _ , lift c≤x) =
      lift (≤-trans a≤c c≤x)

------------------------------------------------------------------------------
-- Day from Promonoids
record IsPromonoid (R : A → A → A → Prop bℓ) (J : A → Prop bℓ) : Prop (aℓ ⊔ℓ bℓ) where
  field
    R-mono   : ∀ {x₁ x₂ y₁ y₂ z₁ z₂} → x₂ ≤ x₁ → y₁ ≤ y₂ → z₁ ≤ z₂ → R x₁ y₁ z₁ → R x₂ y₂ z₂
    J-mono   : ∀ {x₁ x₂} → x₂ ≤ x₁ → J x₁ → J x₂
    R-assoc₁ : ∀ {a a₁ x y z} → R a a₁ z → R a₁ x y → ∃ A λ a₂ → R a x a₂ ∧ R a₂ y z
    R-assoc₂ : ∀ {a a₁ x y z} → R a x a₁ → R a₁ y z → ∃ A λ a₂ → R a a₂ z ∧ R a₂ x y
    R-lunit₁ : ∀ {a x y} → R a x y → J x → a ≤ y
    R-lunit₂ : ∀ {a y} → a ≤ y → ∃ A λ x → R a x y ∧ J x
    R-runit₁ : ∀ {a x y} → R a x y → J y → a ≤ x
    R-runit₂ : ∀ {a x} → a ≤ x → ∃ A λ y → R a x y ∧ J y

module _ {_∙_ ε} (isMonoid : IsMonoid ≤-isPreorder _∙_ ε) where

  open IsMonoid isMonoid
  open IsPromonoid

  monoid→promonoid : IsPromonoid (λ x y z → x ≤ (y ∙ z)) (λ x → x ≤ ε)
  monoid→promonoid .R-mono x₂≤x₁ y₁≤y₂ z₁≤z₂ x₁≤y₁z₁ =
    ≤-trans x₂≤x₁ (≤-trans x₁≤y₁z₁ (mono y₁≤y₂ z₁≤z₂))
  monoid→promonoid .J-mono = ≤-trans
  monoid→promonoid .R-assoc₁ a≤a₁z a₁≤xy =
    _ , (≤-trans a≤a₁z (≤-trans (mono a₁≤xy ≤-refl) (assoc .proj₁))) , ≤-refl
  monoid→promonoid .R-assoc₂ a≤xa₁ a₁≤yz =
    _ , ≤-trans a≤xa₁ (≤-trans (mono ≤-refl a₁≤yz) (assoc .proj₂)) , ≤-refl
  monoid→promonoid .R-lunit₁ a≤xy x≤ε = ≤-trans a≤xy (≤-trans (mono x≤ε ≤-refl) (lunit .proj₁))
  monoid→promonoid .R-lunit₂ a≤y = ε , ≤-trans a≤y (lunit .proj₂) , ≤-refl
  monoid→promonoid .R-runit₁ a≤xy y≤ε = ≤-trans a≤xy (≤-trans (mono ≤-refl y≤ε) (runit .proj₁))
  monoid→promonoid .R-runit₂ a≤x = ε , ≤-trans a≤x (runit .proj₂) , ≤-refl

-- Another example: in (A^op × A), arrows are a promonoid

module PromonoidDay {R J} (R-J-isPromonoid : IsPromonoid R J) where

  open IsPromonoid R-J-isPromonoid

  _⊗_ : Elt → Elt → Elt
  (X ⊗ Y) .Carrier a = ∃ A λ a₁ → ∃ A λ a₂ → R a a₁ a₂ ∧ (X .Carrier a₁ ∧ Y .Carrier a₂)
  (X ⊗ Y) .≤-closed a≤b (a₁ , a₂ , Rba₁a₂ , a₁∈X , a₂∈Y) =
    a₁ , a₂ , R-mono a≤b ≤-refl ≤-refl Rba₁a₂ , a₁∈X , a₂∈Y

  I : Elt
  I .Carrier a = LiftP (aℓ ⊔ℓ cℓ) (J a)
  I .≤-closed a≤b (lift a∈J) = lift (J-mono a≤b a∈J)

  ⊗-isMonoid : IsMonoid ⊑-isPreorder _⊗_ I
  ⊗-isMonoid .IsMonoid.mono X₁⊑X₂ Y₁⊑Y₂ .*≤* (x , y , Raxy , x∈X₁ , y∈Y₁) =
    x , y , Raxy , X₁⊑X₂ .*≤* x∈X₁ , Y₁⊑Y₂ .*≤* y∈Y₁
  ⊗-isMonoid .IsMonoid.assoc .proj₁ .*≤* (a₁ , z , Raa₁a₂ , (x , y , Ra₁xy , x∈X , y∈Y) , z∈Z) with R-assoc₁ Raa₁a₂ Ra₁xy
  ... | a' , Raxa' , Ra'yz =
    x , a' , Raxa' , x∈X , y , z , Ra'yz , y∈Y , z∈Z
  ⊗-isMonoid .IsMonoid.assoc .proj₂ .*≤* (x , b , Raxb , x∈X , (y , z , Rbyz , y∈Y , z∈Z)) with R-assoc₂ Raxb Rbyz
  ... | a' , Raa'z , Ra'xy =
    a' , z , Raa'z , (x , y , Ra'xy , x∈X , y∈Y) , z∈Z
  ⊗-isMonoid .IsMonoid.lunit {X} .proj₁ .*≤* (a₁ , a₂ , Raa₁a₂ , lift a₁∈J , a₂∈X) =
    X .≤-closed (R-lunit₁ Raa₁a₂ a₁∈J) a₂∈X
  ⊗-isMonoid .IsMonoid.lunit {X} .proj₂ .*≤* {a} a∈X with R-lunit₂ ≤-refl
  ... | x , Raxa , x∈J = x , a , Raxa , lift x∈J , a∈X
  ⊗-isMonoid .IsMonoid.runit {X} .proj₁ .*≤* (x , y , Raxy , x∈X , lift y∈J) =
    X .≤-closed (R-runit₁ Raxy y∈J) x∈X
  ⊗-isMonoid .IsMonoid.runit {X} .proj₂ .*≤* {a} a∈X with R-runit₂ ≤-refl
  ... | y , Raay , y∈J = a , y , Raay , a∈X , lift y∈J

  -- Distributivity wrt joins
  ⊗-⋃-distribₗ : ∀ {I X Y} → (⋃ I X ⊗ Y) ≃ ⋃ I (λ i → X i ⊗ Y)
  ⊗-⋃-distribₗ .proj₁ .*≤* (a₁ , a₂ , Raa₁a₂ , (i , a₁∈Xi) , a₂∈Y) =
    i , a₁ , a₂ , Raa₁a₂ , a₁∈Xi , a₂∈Y
  ⊗-⋃-distribₗ .proj₂ .*≤* (i , a₁ , a₂ , Raa₁a₂ , a₁∈Xi , a₂∈Y)   =
    a₁ , a₂ , Raa₁a₂ , (i , a₁∈Xi) , a₂∈Y

  ⊗-⋃-distribᵣ : ∀ {I X Y} → (X ⊗ ⋃ I Y) ≃ ⋃ I (λ i → X ⊗ Y i)
  ⊗-⋃-distribᵣ .proj₁ .*≤* (a₁ , a₂ , Raa₁a₂ , a₁∈X , (i , a₂∈Yi)) =
    i , a₁ , a₂ , Raa₁a₂ , a₁∈X , a₂∈Yi
  ⊗-⋃-distribᵣ .proj₂ .*≤* (i , a₁ , a₂ , Raa₁a₂ , a₁∈X , a₂∈Yi)   =
    a₁ , a₂ , Raa₁a₂ , a₁∈X , (i , a₂∈Yi)

  -- Left residual
  _>->_ : Elt → Elt → Elt
  (X >-> Y) .Carrier a = ∀ c d → X .Carrier c → R d a c → Y .Carrier d
  (X >-> Y) .≤-closed a≤b f c d c∈X Rdac = f c d c∈X (R-mono ≤-refl a≤b ≤-refl Rdac)

  -- Right residual
  _->>_ : Elt → Elt → Elt
  (X ->> Y) .Carrier a = ∀ c d → X .Carrier c → R d c a → Y .Carrier d
  (X ->> Y) .≤-closed a≤b f c d c∈X Rdca = f c d c∈X (R-mono ≤-refl ≤-refl a≤b Rdca)

  -- FIXME: state and prove that these are residuals

------------------------------------------------------------------------------
module CommutativePromonoid {R J}
         (R-J-isPromonoid : IsPromonoid R J)
         (R-comm : ∀ {a x y} → R a x y → R a y x)
         where

  open IsPromonoid R-J-isPromonoid
  open PromonoidDay R-J-isPromonoid public

  ⊗-comm : ∀ {X Y} → (X ⊗ Y) ⊑ (Y ⊗ X)
  ⊗-comm .*≤* (x , y , Raxy , x∈X , y∈Y) =
    y , x , R-comm Raxy , y∈Y , x∈X

  -- A notion of “resource free” element of the algebra, defined
  -- intrinsically to the original promonoid.
  --
  -- FIXME: how does this compare to Gratzer et al's idempotent
  -- modality in Iris (ESOP'25)?
  module FreeExponential where

    □ : Elt → Elt
    □ X .Carrier a = ∃ A λ c → (a ≤ c) ∧ (J c ∧ (R c c c ∧ X .Carrier c))
    □ X .≤-closed a≤b (c , b≤c , c∈J , Rccc , c∈X) = c , ≤-trans a≤b b≤c , c∈J , Rccc , c∈X

    □-mono : ∀ {X Y} → X ⊑ Y → □ X ⊑ □ Y
    □-mono X⊑Y .*≤* (c , a≤c , c∈J , Rccc , c∈X) = c , a≤c , c∈J , Rccc , X⊑Y .*≤* c∈X

{-
    -- Raa₁a₂ ∧ Ra₁c₁c₁ ⇒ ∃ x. Rac₁x ∧ Rxc₁a₂
    -- Rxc₁a₂ ∧ Ra₂c₂c₂ ⇒ ∃ y. Rxc₂y ∧ Ryc₁c₂

    □-monoidal : ∀ {X Y} → (□ X ⊗ □ Y) ⊑ □ (X ⊗ Y)
    □-monoidal .*≤* {a} (a₁ , a₂ , Raa₁a₂ , (c₁ , a₁≤c₁ , Jc₁ , Rc₁c₁c₁ , c₁∈X) ,
                                            (c₂ , a₂≤c₂ , Jc₂ , Rc₂c₂c₂ , c₂∈X) ) with R-assoc₁ Raa₁a₂ (R-mono a₁≤c₁ ≤-refl ≤-refl Rc₁c₁c₁)
    ... | x , Rac₁x , Rxc₁a₁ with R-assoc₂ Rxc₁a₁ (R-mono a₂≤c₂ ≤-refl ≤-refl Rc₂c₂c₂)
    ... | y , Rxyc₂ , Ryc₁c₂ =
      y ,
      ≤-trans (R-lunit₁ Rac₁x Jc₁) (R-runit₁ Rxyc₂ Jc₂) ,
      J-mono (R-runit₁ Ryc₁c₂ Jc₂) Jc₁ ,
      {!!} ,
      c₁ , c₂ , Ryc₁c₂ , c₁∈X , c₂∈X

    -- R a c₁ x
    -- R c c₁ a₁
    -- R x y c₂
    -- R y c₁ c₂
    -- R c₁ c₁ c₁
    -- R c₂ c₂ c₂
-}
    □-discard : ∀ {X} → □ X ⊑ I
    □-discard .*≤* (c , a≤c , Jc , _ , _) = lift (J-mono a≤c Jc)

    □-duplicate : ∀ {X} → □ X ⊑ (□ X ⊗ □ X)
    □-duplicate .*≤* (c , a≤c , Jc , Rccc , c∈X) =
      c , c , R-mono a≤c ≤-refl ≤-refl Rccc ,
      (c , ≤-refl , Jc , Rccc , c∈X) ,
      (c , ≤-refl , Jc , Rccc , c∈X)

    □-derelict : ∀ {X} → □ X ⊑ X
    □-derelict {X} .*≤* (c , a≤c , _ , _ , c∈X) = X .≤-closed a≤c c∈X

    □-dig : ∀ {X} → □ X ⊑ □ (□ X)
    □-dig .*≤* (c , a≤c , Jc , Rccc , c∈X) =
      c , a≤c , Jc , Rccc , (c , ≤-refl , Jc , Rccc , c∈X)

------------------------------------------------------------------------------
-- If two monoids are duoidal, then their extensions are too.
--
-- FIXME: what is duoidal for promonoids?
module DayDuoidal {_∙_ ε} {_◁_ ι}
    (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ε)
    (◁-isMonoid : IsMonoid ≤-isPreorder _◁_ ι)
    (∙-◁-duoidal : IsDuoidal ≤-isPreorder _∙_ ε _◁_ ι)
  where

  open IsMonoid ∙-isMonoid
    renaming (mono to ∙-mono; assoc to ∙-assoc; lunit to ∙-lunit; runit to ∙-runit)
  open Day ∙-isMonoid
  open Day ◁-isMonoid
    renaming (_⊗_ to _；_; I to J; ⊗-isMonoid to ；-isMonoid)
  open IsDuoidal ∙-◁-duoidal

  duoidal : IsDuoidal ⊑-isPreorder _⊗_ I _；_ J
  duoidal .IsDuoidal.exchange .*≤* (a₁ , a₂ , a≤a₁a₂ , (b₁ , b₂ , a₁≤b₁b₂ , b₁∈W , b₂∈X) ,
                                                       (c₁ , c₂ , a₂≤c₁c₂ , c₁∈Y , c₂∈Z)) =
    (b₁ ∙ c₁) , (b₂ ∙ c₂) ,
    ≤-trans a≤a₁a₂ (≤-trans (∙-mono a₁≤b₁b₂ a₂≤c₁c₂) exchange) ,
    (b₁ , c₁ , ≤-refl , b₁∈W , c₁∈Y) ,
    b₂ , c₂ , ≤-refl , b₂∈X , c₂∈Z
  duoidal .IsDuoidal.mu .*≤* (a₁ , a₂ , a≤a₁a₂ , lift a₁≤ι , lift a₂≤ι) =
    lift (≤-trans a≤a₁a₂ (≤-trans (∙-mono a₁≤ι a₂≤ι) mu))
  duoidal .IsDuoidal.nu .*≤* (lift a≤ε) = ε , ε , ≤-trans a≤ε nu , lift ≤-refl , lift ≤-refl
  duoidal .IsDuoidal.gu .*≤* (lift a≤ε) = lift (≤-trans a≤ε gu)
