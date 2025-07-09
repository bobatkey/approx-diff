{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level
  using ( _⊔_ )
open import basics
  using ( IsPreorder; IsMonoid; IsResidual; IsExponential; IsMeet; IsJoin;
          module ≤-Reasoning; ∙-∨-distrib; IsStarAuto )
open import prop
  using ( proj₁; proj₂ )

module chu
  {a p} {A : Set a} {_≤_ : A → A → Prop p} (≤-isPreorder : IsPreorder _≤_)
  {_∙_ ε} (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ε)
  (comm : ∀ {x y} → (x ∙ y) ≤ (y ∙ x))
  {_-∙_} (-∙-isResidual : IsResidual ≤-isPreorder ∙-isMonoid _-∙_)
  {_∧_} (∧-isMeet : IsMeet ≤-isPreorder _∧_)
  {_∨_} (∨-isJoin : IsJoin ≤-isPreorder _∨_)
  (K : A)
  where

record Elt : Set (a ⊔ p) where
  no-eta-equality
  field
    pos : A
    neg : A
    int : (pos ∙ neg) ≤ K
open Elt

record _⊑_ (X Y : Elt) : Prop p where
  no-eta-equality
  field
    fpos : X .pos ≤ Y .pos
    fneg : Y .neg ≤ X .neg
open _⊑_

open IsPreorder ≤-isPreorder
  renaming (refl to ≤-refl; trans to ≤-trans;
            _≃_ to _≈_; ≃-refl to ≈-refl; ≃-trans to ≈-trans; ≃-sym to ≈-sym;
            isEquivalence to ≈-isEquivalence)

private
  module M = IsMonoid ∙-isMonoid
  module R = IsResidual -∙-isResidual
  module C = IsMeet ∧-isMeet
  module D = IsJoin ∨-isJoin

⊑-refl : ∀ {X} → X ⊑ X
⊑-refl .fpos = ≤-refl
⊑-refl .fneg = ≤-refl

⊑-trans : ∀ {X Y Z} → X ⊑ Y → Y ⊑ Z → X ⊑ Z
⊑-trans X⊑Y Y⊑Z .fpos = ≤-trans (X⊑Y .fpos) (Y⊑Z .fpos)
⊑-trans X⊑Y Y⊑Z .fneg = ≤-trans (Y⊑Z .fneg) (X⊑Y .fneg)

⊑-isPreorder : IsPreorder _⊑_
⊑-isPreorder .IsPreorder.refl = ⊑-refl
⊑-isPreorder .IsPreorder.trans = ⊑-trans

open IsPreorder ⊑-isPreorder
  hiding (refl; trans)

------------------------------------------------------------------------------
-- Embedding and forgeting

embed : A → Elt
embed x .pos = x
embed x .neg = x -∙ K
embed x .int = ≤-trans comm R.eval

embed-mono : ∀ {x y} → x ≤ y → embed x ⊑ embed y
embed-mono x≤y .fpos = x≤y
embed-mono x≤y .fneg = R.lambda (≤-trans (M.mono ≤-refl x≤y) R.eval)

U : Elt → A
U X = X .pos

U-mono : ∀ {X Y} → X ⊑ Y → U X ≤ U Y
U-mono X⊑Y = X⊑Y .fpos

counit : ∀ {X} → embed (U X) ⊑ X
counit {X} .fpos = ≤-refl
counit {X} .fneg = R.lambda (≤-trans comm (X .int))

unit : ∀ {x} → x ≈ U (embed x)
unit = ≈-refl

------------------------------------------------------------------------------
-- Monoid
I : Elt
I .pos = ε
I .neg = K
I .int = M.lunit .proj₁

_⊗_ : Elt → Elt → Elt
(X ⊗ Y) .pos = X .pos ∙ Y .pos
(X ⊗ Y) .neg = (X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg)
(X ⊗ Y) .int =
   begin
     (X .pos ∙ Y .pos) ∙ ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg))
   ≤⟨ M.mono ≤-refl C.π₂ ⟩
     (X .pos ∙ Y .pos) ∙ (Y .pos -∙ X .neg)
   ≤⟨ M.assoc .proj₁ ⟩
     X .pos ∙ (Y .pos ∙ (Y .pos -∙ X .neg))
   ≤⟨ M.mono ≤-refl comm ⟩
     X .pos ∙ ((Y .pos -∙ X .neg) ∙ Y .pos)
   ≤⟨ M.mono ≤-refl R.eval ⟩
     X .pos ∙ X .neg
   ≤⟨ X .int ⟩
     K
   ∎
   where open ≤-Reasoning ≤-isPreorder

⊗-mono : ∀ {X₁ X₂ Y₁ Y₂} → X₁ ⊑ X₂ → Y₁ ⊑ Y₂ → (X₁ ⊗ Y₁) ⊑ (X₂ ⊗ Y₂)
⊗-mono X₁⊑X₂ Y₁⊑Y₂ .fpos = M.mono (X₁⊑X₂ .fpos) (Y₁⊑Y₂ .fpos)
⊗-mono X₁⊑X₂ Y₁⊑Y₂ .fneg =
  C.mono (R.-∙-mono (X₁⊑X₂ .fpos) (Y₁⊑Y₂ .fneg))
         (R.-∙-mono (Y₁⊑Y₂ .fpos) (X₁⊑X₂ .fneg))

⊗-lunit : ∀ {X} → (I ⊗ X) ≃ X
⊗-lunit .proj₁ .fpos = M.lunit .proj₁
⊗-lunit {X} .proj₁ .fneg =
  C.⟨ R.lambda (M.runit .proj₁)
    , R.lambda (≤-trans comm (X .int)) ⟩
⊗-lunit .proj₂ .fpos = M.lunit .proj₂
⊗-lunit .proj₂ .fneg =
  ≤-trans C.π₁ (≤-trans (M.runit .proj₂) R.eval)

⊗-runit : ∀ {X} → (X ⊗ I) ≃ X
⊗-runit {X} .proj₁ .fpos = M.runit .proj₁
⊗-runit {X} .proj₁ .fneg = C.⟨ R.lambda (≤-trans comm (X .int)) , R.lambda (M.runit .proj₁) ⟩
⊗-runit {X} .proj₂ .fpos = M.runit .proj₂
⊗-runit {X} .proj₂ .fneg = ≤-trans C.π₂ (≤-trans (M.runit .proj₂) R.eval)

⊗-assoc : ∀ {X Y Z} → ((X ⊗ Y) ⊗ Z) ≃ (X ⊗ (Y ⊗ Z))
⊗-assoc {X} {Y} {Z} .proj₁ .fpos = M.assoc .proj₁
⊗-assoc {X} {Y} {Z} .proj₁ .fneg = C.⟨ R.lambda lem₁ , R.lambda C.⟨ R.lambda lem₂ , R.lambda lem₃ ⟩ ⟩
  where open ≤-Reasoning ≤-isPreorder
        lem₁ : (((X .pos -∙ ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg))) ∧ ((Y .pos ∙ Z .pos) -∙ X .neg)) ∙ (X .pos ∙ Y .pos)) ≤ Z .neg
        lem₁ = begin
            ((X .pos -∙ ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg))) ∧ ((Y .pos ∙ Z .pos) -∙ X .neg)) ∙ (X .pos ∙ Y .pos)
          ≤⟨ M.mono C.π₁ ≤-refl ⟩
            (X .pos -∙ ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg))) ∙ (X .pos ∙ Y .pos)
          ≤⟨ M.assoc .proj₂ ⟩
            ((X .pos -∙ ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg))) ∙ X .pos) ∙ Y .pos
          ≤⟨ M.mono R.eval ≤-refl ⟩
            ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg)) ∙ Y .pos
          ≤⟨ M.mono C.π₁ ≤-refl ⟩
            (Y .pos -∙ Z .neg) ∙ Y .pos
          ≤⟨ R.eval ⟩
            Z .neg
          ∎
        lem₂ : ((((X .pos -∙ ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg))) ∧ ((Y .pos ∙ Z .pos) -∙ X .neg)) ∙ Z .pos) ∙ X .pos) ≤ Y .neg
        lem₂ = begin
            (((X .pos -∙ ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg))) ∧ ((Y .pos ∙ Z .pos) -∙ X .neg)) ∙ Z .pos) ∙ X .pos
          ≤⟨ M.mono (M.mono C.π₁ ≤-refl) ≤-refl ⟩
            ((X .pos -∙ ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg))) ∙ Z .pos) ∙ X .pos
          ≤⟨ M.assoc .proj₁ ⟩
            (X .pos -∙ ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg))) ∙ (Z .pos ∙ X .pos)
          ≤⟨ M.mono ≤-refl comm ⟩
            (X .pos -∙ ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg))) ∙ (X .pos ∙ Z .pos)
          ≤⟨ M.assoc .proj₂ ⟩
            ((X .pos -∙ ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg))) ∙ X .pos) ∙ Z .pos
          ≤⟨ M.mono R.eval ≤-refl ⟩
            ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg)) ∙ Z .pos
          ≤⟨ M.mono C.π₂ ≤-refl ⟩
            (Z .pos -∙ Y .neg) ∙ Z .pos
          ≤⟨ R.eval ⟩
            Y .neg
          ∎
        lem₃ : ((((X .pos -∙ ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg))) ∧ ((Y .pos ∙ Z .pos) -∙ X .neg)) ∙ Z .pos) ∙ Y .pos) ≤ X .neg
        lem₃ = begin
            (((X .pos -∙ ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg))) ∧ ((Y .pos ∙ Z .pos) -∙ X .neg)) ∙ Z .pos) ∙ Y .pos
          ≤⟨ M.assoc .proj₁ ⟩
            ((X .pos -∙ ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg))) ∧ ((Y .pos ∙ Z .pos) -∙ X .neg)) ∙ (Z .pos ∙ Y .pos)
          ≤⟨ M.mono C.π₂ comm ⟩
            ((Y .pos ∙ Z .pos) -∙ X .neg) ∙ (Y .pos ∙ Z .pos)
          ≤⟨ R.eval ⟩
            X .neg
          ∎
⊗-assoc .proj₂ .fpos = M.assoc .proj₂
⊗-assoc {X} {Y} {Z} .proj₂ .fneg = C.⟨ R.lambda C.⟨ R.lambda lem₁ , R.lambda lem₂ ⟩ , R.lambda lem₃ ⟩
  where open ≤-Reasoning ≤-isPreorder
        lem₁ : (((((X .pos ∙ Y .pos) -∙ Z .neg) ∧ (Z .pos -∙ ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg)))) ∙ X .pos) ∙ Y .pos) ≤ Z .neg
        lem₁ = begin
            ((((X .pos ∙ Y .pos) -∙ Z .neg) ∧ (Z .pos -∙ ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg)))) ∙ X .pos) ∙ Y .pos
          ≤⟨ M.assoc .proj₁ ⟩
            (((X .pos ∙ Y .pos) -∙ Z .neg) ∧ (Z .pos -∙ ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg)))) ∙ (X .pos ∙ Y .pos)
          ≤⟨ M.mono C.π₁ ≤-refl ⟩
            ((X .pos ∙ Y .pos) -∙ Z .neg) ∙ (X .pos ∙ Y .pos)
          ≤⟨ R.eval ⟩
            Z .neg
          ∎
        lem₂ : (((((X .pos ∙ Y .pos) -∙ Z .neg) ∧ (Z .pos -∙ ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg)))) ∙ X .pos) ∙ Z .pos) ≤ Y .neg
        lem₂ = begin
            ((((X .pos ∙ Y .pos) -∙ Z .neg) ∧ (Z .pos -∙ ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg)))) ∙ X .pos) ∙ Z .pos
          ≤⟨ M.assoc .proj₁ ⟩
            (((X .pos ∙ Y .pos) -∙ Z .neg) ∧ (Z .pos -∙ ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg)))) ∙ (X .pos ∙ Z .pos)
          ≤⟨ M.mono C.π₂ comm ⟩
            (Z .pos -∙ ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg))) ∙ (Z .pos ∙ X .pos)
          ≤⟨ M.assoc .proj₂ ⟩
            ((Z .pos -∙ ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg))) ∙ Z .pos) ∙ X .pos
          ≤⟨ M.mono R.eval ≤-refl ⟩
            ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg)) ∙ X .pos
          ≤⟨ M.mono C.π₁ ≤-refl ⟩
            (X .pos -∙ Y .neg) ∙ X .pos
          ≤⟨ R.eval ⟩
            Y .neg
          ∎
        lem₃ : ((((X .pos ∙ Y .pos) -∙ Z .neg) ∧ (Z .pos -∙ ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg)))) ∙ (Y .pos ∙ Z .pos)) ≤ X .neg
        lem₃ = begin
            (((X .pos ∙ Y .pos) -∙ Z .neg) ∧ (Z .pos -∙ ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg)))) ∙ (Y .pos ∙ Z .pos)
          ≤⟨ M.mono C.π₂ comm ⟩
            (Z .pos -∙ ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg))) ∙ (Z .pos ∙ Y .pos)
          ≤⟨ M.assoc .proj₂ ⟩
            ((Z .pos -∙ ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg))) ∙ Z .pos) ∙ Y .pos
          ≤⟨ M.mono R.eval ≤-refl ⟩
            ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg)) ∙ Y .pos
          ≤⟨ M.mono C.π₂ ≤-refl ⟩
            (Y .pos -∙ X .neg) ∙ Y .pos
          ≤⟨ R.eval ⟩
            X .neg
          ∎

⊗-comm : ∀ {X Y} → (X ⊗ Y) ⊑ (Y ⊗ X)
⊗-comm .fpos = comm
⊗-comm .fneg = C.comm

⊗-isMonoid : IsMonoid ⊑-isPreorder _⊗_ I
⊗-isMonoid .IsMonoid.mono = ⊗-mono
⊗-isMonoid .IsMonoid.assoc = ⊗-assoc
⊗-isMonoid .IsMonoid.lunit = ⊗-lunit
⊗-isMonoid .IsMonoid.runit = ⊗-runit

embed-⊗ : ∀ {x y} → (embed x ⊗ embed y) ≃ embed (x ∙ y)
embed-⊗ .proj₁ .fpos = ≤-refl
embed-⊗ .proj₁ .fneg = C.⟨ R.lambda (R.lambda (≤-trans (M.assoc .proj₁) R.eval))
                         , R.lambda (R.lambda (≤-trans (M.assoc .proj₁) (≤-trans (M.mono ≤-refl comm) R.eval))) ⟩
embed-⊗ .proj₂ .fpos = ≤-refl
embed-⊗ .proj₂ .fneg = ≤-trans C.π₁ (R.lambda (≤-trans (M.assoc .proj₂) (≤-trans (M.mono R.eval ≤-refl) R.eval)))

------------------------------------------------------------------------------
-- Duality
¬ : Elt → Elt
¬ X .pos = X .neg
¬ X .neg = X .pos
¬ X .int = ≤-trans comm (X .int)

¬-mono : ∀ {X Y} → X ⊑ Y → ¬ Y ⊑ ¬ X
¬-mono X⊑Y .fpos = X⊑Y .fneg
¬-mono X⊑Y .fneg = X⊑Y .fpos

------------------------------------------------------------------------------
-- *-autonomous poset

isStarAut : IsStarAuto ⊑-isPreorder ⊗-isMonoid ⊗-comm ¬
isStarAut .IsStarAuto.¬-mono = ¬-mono
isStarAut .IsStarAuto.involution .proj₁ = record { fpos = ≤-refl ; fneg = ≤-refl }
isStarAut .IsStarAuto.involution .proj₂ = record { fpos = ≤-refl ; fneg = ≤-refl }
isStarAut .IsStarAuto.*-aut {X} {Y} {Z} XY⊑¬Z .fpos = C.⟨ (R.lambda (XY⊑¬Z .fpos)) , (R.lambda lem) ⟩
  where open ≤-Reasoning ≤-isPreorder
        lem : (X .pos ∙ Z .pos) ≤ Y .neg
        lem = begin
            X .pos ∙ Z .pos
          ≤⟨ comm ⟩
            Z .pos ∙ X .pos
          ≤⟨ M.mono (XY⊑¬Z .fneg) ≤-refl ⟩
            ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg)) ∙ X .pos
          ≤⟨ M.mono C.π₁ ≤-refl ⟩
            (X .pos -∙ Y .neg) ∙ X .pos
          ≤⟨ R.eval ⟩
            Y .neg
          ∎
isStarAut .IsStarAuto.*-aut {X} {Y} {Z} XY⊑¬Z .fneg = begin
    Y .pos ∙ Z .pos
  ≤⟨ comm ⟩
    Z .pos ∙ Y .pos
  ≤⟨ M.mono (XY⊑¬Z .fneg) ≤-refl ⟩
    ((X .pos -∙ Y .neg) ∧ (Y .pos -∙ X .neg)) ∙ Y .pos
  ≤⟨ M.mono C.π₂ ≤-refl ⟩
    (Y .pos -∙ X .neg) ∙ Y .pos
  ≤⟨ R.eval ⟩
    X .neg
  ∎
  where open ≤-Reasoning ≤-isPreorder
isStarAut .IsStarAuto.*-aut⁻¹ {X} {Y} {Z} X⊑¬⟨YZ⟩ .fpos = begin
    X .pos ∙ Y .pos
  ≤⟨ M.mono (X⊑¬⟨YZ⟩ .fpos) ≤-refl ⟩
    ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg)) ∙ Y .pos
  ≤⟨ M.mono C.π₁ ≤-refl ⟩
    (Y .pos -∙ Z .neg) ∙ Y .pos
  ≤⟨ R.eval ⟩
    Z .neg
  ∎
  where open ≤-Reasoning ≤-isPreorder
isStarAut .IsStarAuto.*-aut⁻¹ {X} {Y} {Z} X⊑¬⟨YZ⟩ .fneg =
  C.⟨ R.lambda lem , R.lambda (≤-trans comm (X⊑¬⟨YZ⟩ .fneg)) ⟩
  where open ≤-Reasoning ≤-isPreorder
        lem : (Z .pos ∙ X .pos) ≤ Y .neg
        lem = begin
            Z .pos ∙ X .pos
          ≤⟨ comm ⟩
            X .pos ∙ Z .pos
          ≤⟨ M.mono (X⊑¬⟨YZ⟩ .fpos) ≤-refl ⟩
            ((Y .pos -∙ Z .neg) ∧ (Z .pos -∙ Y .neg)) ∙ Z .pos
          ≤⟨ M.mono C.π₂ ≤-refl ⟩
            (Z .pos -∙ Y .neg) ∙ Z .pos
          ≤⟨ R.eval ⟩
            Y .neg
          ∎

open IsStarAuto isStarAut hiding (¬-mono)

------------------------------------------------------------------------------
-- Additives

_&_ : Elt → Elt → Elt
(X & Y) .pos = X .pos ∧ Y .pos
(X & Y) .neg = X .neg ∨ Y .neg
(X & Y) .int =
  ≤-trans
    (∙-∨-distrib ≤-isPreorder ∙-isMonoid comm -∙-isResidual ∨-isJoin)
    D.[ ≤-trans (M.mono C.π₁ ≤-refl) (X .int)
      , ≤-trans (M.mono C.π₂ ≤-refl) (Y .int)
      ]

π₁ : ∀ {X Y} → (X & Y) ⊑ X
π₁ .fpos = C.π₁
π₁ .fneg = D.inl

π₂ : ∀ {X Y} → (X & Y) ⊑ Y
π₂ .fpos = C.π₂
π₂ .fneg = D.inr

&-greatest : ∀ {X Y Z} → X ⊑ Y → X ⊑ Z → X ⊑ (Y & Z)
&-greatest X⊑Y X⊑Z .fpos = C.⟨ X⊑Y .fpos , X⊑Z .fpos ⟩
&-greatest X⊑Y X⊑Z .fneg = D.[ X⊑Y .fneg , X⊑Z .fneg ]

&-isMeet : IsMeet ⊑-isPreorder _&_
&-isMeet .IsMeet.π₁ = π₁
&-isMeet .IsMeet.π₂ = π₂
&-isMeet .IsMeet.⟨_,_⟩ = &-greatest

{-
embed-& : ∀ {x y} → (embed x & embed y) ≃ embed (x ∧ y)
embed-& .proj₁ .fpos = ≤-refl
embed-& .proj₁ .fneg = ≤-trans {!!} D.inl
embed-& .proj₂ .fpos = ≤-refl
embed-& .proj₂ .fneg = D.[ R.lambda (≤-trans (M.mono ≤-refl C.π₁) R.eval)
                         , R.lambda (≤-trans (M.mono ≤-refl C.π₂) R.eval)
                         ]
-}

-- dual is _⊕_. FIXME: this works for all *-autonomous posets

_⊕_ : Elt → Elt → Elt
X ⊕ Y = ¬ (¬ X & ¬ Y)

inl : ∀ {X Y} → X ⊑ (X ⊕ Y)
inl = ⊑-trans (involution .proj₁) (¬-mono π₁)

inr : ∀ {X Y} → Y ⊑ (X ⊕ Y)
inr = ⊑-trans (involution .proj₁) (¬-mono π₂)

⊕-least : ∀ {X Y Z} → X ⊑ Z → Y ⊑ Z → (X ⊕ Y) ⊑ Z
⊕-least X⊑Z Y⊑Z =
  ⊑-trans (¬-mono (&-greatest (¬-mono X⊑Z) (¬-mono Y⊑Z))) (involution .proj₂)

⊕-isJoin : IsJoin ⊑-isPreorder _⊕_
⊕-isJoin .IsJoin.inl = inl
⊕-isJoin .IsJoin.inr = inr
⊕-isJoin .IsJoin.[_,_] = ⊕-least

-- & and ⅋ distribute, and so do ⊕ and ⊗, simply by their lattice
-- properties.

------------------------------------------------------------------------------
-- Duoidal operators: if A has another monoid ▷, and ∙ is duoidal over
-- ▷, then this carries over to the Chu preorder.
--
-- FIXME: in light of the below, we can have separate positive and
-- negative parts in the duoidal relationship:
--
--   ((w ⊔ x) ∙ (y ⊓ z)) ≤ (w ∙ y) ⊔ (x ∙ z)
--
-- and   K ⊔ K ≤ K
--
-- if _⊔_ and _⊓_ are monoids, then so is the new operator
--
-- does this new requirement have a nice explanation in terms of
-- linearly distributive functors?

module Binop
    (_⊔_ _⊓_ : A → A → A)
    (⊔-mono : ∀ {x₁ x₂ y₁ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ ⊔ y₁) ≤ (x₂ ⊔ y₂))
    (⊓-mono : ∀ {x₁ x₂ y₁ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ ⊓ y₁) ≤ (x₂ ⊓ y₂))
    (∙-⊓-duoidal : ∀ {w x y z} → ((w ⊓ x) ∙ (y ⊓ z)) ≤ ((w ∙ y) ⊓ (x ∙ z)))
    (confine : ∀ {w x y z} → ((w ⊔ x) ∙ (y ⊓ z)) ≤ ((w ∙ y) ⊔ (x ∙ z)))
    (idem-K  : (K ⊔ K) ≤ K)
  where

  _□_ : Elt → Elt → Elt
  (X □ Y) .pos = X .pos ⊔ Y .pos
  (X □ Y) .neg = X .neg ⊓ Y .neg
  (X □ Y) .int = ≤-trans confine (≤-trans (⊔-mono (X .int) (Y .int)) idem-K)

  _⋄_ : Elt → Elt → Elt
  X ⋄ Y = ¬ (¬ X □ ¬ Y)

  □-mono : ∀ {X₁ X₂ Y₁ Y₂} → X₁ ⊑ X₂ → Y₁ ⊑ Y₂ → (X₁ □ Y₁) ⊑ (X₂ □ Y₂)
  □-mono X₁⊑X₂ Y₁⊑Y₂ .fpos = ⊔-mono (X₁⊑X₂ .fpos) (Y₁⊑Y₂ .fpos)
  □-mono X₁⊑X₂ Y₁⊑Y₂ .fneg = ⊓-mono (X₁⊑X₂ .fneg) (Y₁⊑Y₂ .fneg)

  -- Various “duals” of duoidalness. FIXME: better names
  entropy : ∀ {w x y z} → ((w -∙ y) ⊓ (x -∙ z)) ≤ ((w ⊔ x) -∙ (y ⊔ z))
  entropy = R.lambda (≤-trans comm
                     (≤-trans confine
                     (≤-trans (⊔-mono comm comm)
                              (⊔-mono R.eval R.eval))))

  entropy' : ∀ {w x y z} → ((w -∙ y) ⊔ (x -∙ z)) ≤ ((w ⊓ x) -∙ (y ⊔ z))
  entropy' = R.lambda (≤-trans confine (⊔-mono R.eval R.eval))

  entropy2 : ∀ {w x y z} → ((w -∙ y) ⊓ (x -∙ z)) ≤ ((w ⊓ x) -∙ (y ⊓ z))
  entropy2 = R.lambda (≤-trans ∙-⊓-duoidal (⊓-mono R.eval R.eval))

  -- monotone operators are always duoidal over ∧
  ⊓-medial : ∀ {w x y z} → ((w ∧ x) ⊓ (y ∧ z)) ≤ ((w ⊓ y) ∧ (x ⊓ z))
  ⊓-medial = C.⟨ ⊓-mono C.π₁ C.π₁ , ⊓-mono C.π₂ C.π₂ ⟩

  ⊔-medial : ∀ {w x y z} → ((w ∧ x) ⊔ (y ∧ z)) ≤ ((w ⊔ y) ∧ (x ⊔ z))
  ⊔-medial = C.⟨ ⊔-mono C.π₁ C.π₁ , ⊔-mono C.π₂ C.π₂ ⟩

  -- Now we get the confinement and duoidality relationships
  ⊗-□-confine : ∀ {W X Y Z} → ((W □ X) ⊗ (Y ⋄ Z)) ⊑ ((W ⊗ Y) □ (X ⊗ Z))
  ⊗-□-confine .fpos = confine
  ⊗-□-confine .fneg = ≤-trans ⊓-medial C.⟨ ≤-trans C.π₁ entropy , ≤-trans C.π₂ entropy2 ⟩

  ⊗-□-duoidal : ∀ {W X Y Z} → ((W ⋄ X) ⊗ (Y ⋄ Z)) ⊑ ((W ⊗ Y) ⋄ (X ⊗ Z))
  ⊗-□-duoidal .fpos = ∙-⊓-duoidal
  ⊗-□-duoidal .fneg = ≤-trans ⊔-medial C.⟨ ≤-trans C.π₁ entropy' , ≤-trans C.π₂ entropy' ⟩

  -- If the _⊔_ and _⊓_ are monoids, then so are _□_ and _⋄_. In
  -- general, if they both support some algebra structure, then so do
  -- their Chu versions.

-- Every exponential on A gives an exponential on chu(A,K)
module Exponential
    {！} (！-isExponential : IsExponential ≤-isPreorder ∙-isMonoid ！)
    where

  open IsExponential ！-isExponential
    renaming (mono to ！-mono;
              monoidal-unit to ！-monoidal-unit;
              monoidal-prod to ！-monoidal-prod;
              discard to ！-discard;
              duplicate to ！-duplicate;
              derelict to ！-derelict;
              dig to ！-dig)

  !! : Elt → Elt
  !! X = embed (！ (U X))

  !!-mono : ∀ {X₁ X₂} → X₁ ⊑ X₂ → !! X₁ ⊑ !! X₂
  !!-mono X₁⊑X₂ = embed-mono (！-mono (U-mono X₁⊑X₂))

  !!-monoidal-unit : I ⊑ !! I
  !!-monoidal-unit .fpos = ！-monoidal-unit
  !!-monoidal-unit .fneg =
    ≤-trans (M.runit .proj₂) (≤-trans (M.mono ≤-refl ！-monoidal-unit) R.eval)

  !!-monoidal-prod : ∀ {X Y} → (!! X ⊗ !! Y) ⊑ !! (X ⊗ Y)
  !!-monoidal-prod {X} {Y} .fpos = ！-monoidal-prod
  !!-monoidal-prod {X} {Y} .fneg = C.⟨ R.lambda (R.lambda lem₁) , R.lambda (R.lambda lem₂) ⟩
    where
      lem₁ : (((！ (X .pos ∙ Y .pos) -∙ K) ∙ ！ (X .pos)) ∙ ！ (Y .pos)) ≤ K
      lem₁ = ≤-trans (M.assoc .proj₁)
            (≤-trans (M.mono ≤-refl ！-monoidal-prod)
                     R.eval)

      lem₂ : (((！ (X .pos ∙ Y .pos) -∙ K) ∙ ！ (Y .pos)) ∙ ！ (X .pos)) ≤ K
      lem₂ = ≤-trans (M.assoc .proj₁)
            (≤-trans (M.mono ≤-refl comm)
            (≤-trans (M.mono ≤-refl ！-monoidal-prod)
                     R.eval))

  !!-discard : ∀ {X} → !! X ⊑ I
  !!-discard .fpos = ！-discard
  !!-discard .fneg = R.lambda (≤-trans (M.mono ≤-refl ！-discard) (M.runit .proj₁))

  !!-duplicate : ∀ {X} → !! X ⊑ (!! X ⊗ !! X)
  !!-duplicate .fpos = ！-duplicate
  !!-duplicate .fneg = ≤-trans C.π₁ (R.lambda (≤-trans (M.mono ≤-refl ！-duplicate)
                                              (≤-trans (M.assoc .proj₂)
                                              (≤-trans (M.mono R.eval ≤-refl)
                                                       R.eval))))

  !!-derelict : ∀ {X} → !! X ⊑ X
  !!-derelict {X} .fpos = ！-derelict
  !!-derelict {X} .fneg = R.lambda (≤-trans (M.mono ≤-refl ！-derelict)
                                   (≤-trans comm (X .int)))

  !!-dig : ∀ {X} → !! X ⊑ !! (!! X)
  !!-dig .fpos = ！-dig
  !!-dig .fneg = R.lambda (≤-trans (M.mono ≤-refl ！-dig) R.eval)

  !!-isExponential : IsExponential ⊑-isPreorder ⊗-isMonoid !!
  !!-isExponential .IsExponential.mono = !!-mono
  !!-isExponential .IsExponential.monoidal-unit = !!-monoidal-unit
  !!-isExponential .IsExponential.monoidal-prod {X} {Y} = !!-monoidal-prod {X} {Y}
  !!-isExponential .IsExponential.discard {X} = !!-discard {X}
  !!-isExponential .IsExponential.duplicate {X} = !!-duplicate {X}
  !!-isExponential .IsExponential.derelict = !!-derelict
  !!-isExponential .IsExponential.dig {X} = !!-dig {X}

  -- FIXME: get a dual ?? monad too.
