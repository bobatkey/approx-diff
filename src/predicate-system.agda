{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (suc; _⊔_; 0ℓ)
open import basics
  using (IsPreorder; IsTop; IsMeet; IsResidual; monoidOfMeet; module ≤-Reasoning; IsJoin; IsClosureOp; IsBigJoin)
open import categories using (Category; HasProducts; HasExponentials)

module predicate-system {o m e} (𝒞 : Category o m e) (P : HasProducts 𝒞) where

private
  module 𝒞 = Category 𝒞
  module P = HasProducts P

record PredicateSystem : Set (suc (suc (o ⊔ m ⊔ e))) where
  field
    Predicate : 𝒞.obj → Set (suc o ⊔ suc m ⊔ suc e)
    _⊑_   : ∀ {X : 𝒞.obj} → Predicate X → Predicate X → Prop (o ⊔ m ⊔ e)
    ⊑-isPreorder : ∀ {X} → IsPreorder (_⊑_ {X})

  infix 2 _⊑_

  ⊑-trans : ∀ {X} {P Q R : Predicate X} → P ⊑ Q → Q ⊑ R → P ⊑ R
  ⊑-trans = ⊑-isPreorder .IsPreorder.trans

  field
    _[_]   : ∀ {X Y} → Predicate Y → X 𝒞.⇒ Y → Predicate X
    _⟨_⟩   : ∀ {X Y} → Predicate X → X 𝒞.⇒ Y → Predicate Y

    _[_]m     : ∀ {X Y} {P Q : Predicate Y} → P ⊑ Q → (f : X 𝒞.⇒ Y) → (P [ f ]) ⊑ (Q [ f ])
    []-cong   : ∀ {X Y} {P : Predicate Y}{f₁ f₂ : X 𝒞.⇒ Y} → f₁ 𝒞.≈ f₂ → (P [ f₁ ]) ⊑ (P [ f₂ ])
    []-id     : ∀ {X} {P : Predicate X} → P ⊑ (P [ 𝒞.id _ ])
    []-id⁻¹   : ∀ {X} {P : Predicate X} → (P [ 𝒞.id _ ]) ⊑ P
    []-comp   : ∀ {X Y Z} {P : Predicate Z} (f : Y 𝒞.⇒ Z) (g : X 𝒞.⇒ Y) → ((P [ f ]) [ g ]) ⊑ (P [ f 𝒞.∘ g ])
    []-comp⁻¹ : ∀ {X Y Z} {P : Predicate Z} (f : Y 𝒞.⇒ Z) (g : X 𝒞.⇒ Y) → (P [ f 𝒞.∘ g ]) ⊑ ((P [ f ]) [ g ])

    adjoint₁ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} {f : X 𝒞.⇒ Y} → P ⟨ f ⟩ ⊑ Q → P ⊑ Q [ f ]
    adjoint₂ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} {f : X 𝒞.⇒ Y} → P ⊑ Q [ f ] → P ⟨ f ⟩ ⊑ Q

  unit : ∀ {X Y} {P : Predicate X} (f : X 𝒞.⇒ Y) → P ⊑ P ⟨ f ⟩ [ f ]
  unit f = adjoint₁ (IsPreorder.refl ⊑-isPreorder)

  counit : ∀ {X Y} {P : Predicate Y} (f : X 𝒞.⇒ Y) → P [ f ] ⟨ f ⟩ ⊑ P
  counit f = adjoint₂ (IsPreorder.refl ⊑-isPreorder)

  _⟨_⟩m : ∀ {X Y} {P Q : Predicate X} → P ⊑ Q → (f : X 𝒞.⇒ Y) → (P ⟨ f ⟩) ⊑ (Q ⟨ f ⟩)
  P⊑Q ⟨ f ⟩m = adjoint₂ (IsPreorder.trans ⊑-isPreorder P⊑Q (unit f))

  ⟨⟩-comp : ∀ {X Y Z} {P : Predicate X} (f : Y 𝒞.⇒ Z) (g : X 𝒞.⇒ Y) → (P ⟨ g ⟩ ⟨ f ⟩) ⊑ (P ⟨ f 𝒞.∘ g ⟩)
  ⟨⟩-comp f g = adjoint₂ (adjoint₂ (⊑-trans (unit _) ([]-comp⁻¹ f g)))

  ⟨⟩-cong : ∀ {X Y} {P : Predicate X}{f₁ f₂ : X 𝒞.⇒ Y} → f₁ 𝒞.≈ f₂ → (P ⟨ f₁ ⟩) ⊑ (P ⟨ f₂ ⟩)
  ⟨⟩-cong f₁≈f₂ = adjoint₂ (⊑-trans (unit _) ([]-cong (𝒞.≈-sym f₁≈f₂)))

  field
    TT    : ∀ {X} → Predicate X
    _&&_  : ∀ {X} → Predicate X → Predicate X → Predicate X
    _++_  : ∀ {X} → Predicate X → Predicate X → Predicate X
    _==>_ : ∀ {X} → Predicate X → Predicate X → Predicate X
    ⋀     : ∀ {X Y} → Predicate (P.prod X Y) → Predicate X

    TT-isTop  : ∀ {X} → IsTop ⊑-isPreorder (TT {X})
    []-TT     : ∀ {X Y} {f : X 𝒞.⇒ Y} → TT ⊑ TT [ f ]

    &&-isMeet : ∀ {X} → IsMeet ⊑-isPreorder (_&&_ {X})
    []-&&     : ∀ {X Y} {P Q : Predicate Y} {f : X 𝒞.⇒ Y} → ((P [ f ]) && (Q [ f ])) ⊑ ((P && Q) [ f ])

    ++-isJoin : ∀ {X} → IsJoin ⊑-isPreorder (_++_ {X})
    []-++     : ∀ {X Y} {P Q : Predicate Y} {f : X 𝒞.⇒ Y} → ((P ++ Q) [ f ]) ⊑ ((P [ f ]) ++ (Q [ f ]))

    ==>-residual : ∀ {X} → IsResidual ⊑-isPreorder (monoidOfMeet _ &&-isMeet TT-isTop) (_==>_ {X})
    []-==> : ∀ {X Y}{P Q : Predicate Y}{f : X 𝒞.⇒ Y} → ((P [ f ]) ==> (Q [ f ])) ⊑ (P ==> Q) [ f ]

    ⋀-[] : ∀ {X X' Y} {P : Predicate (P.prod X Y)} {f : X' 𝒞.⇒ X} → (⋀ (P [ P.prod-m f (𝒞.id _) ])) ⊑ (⋀ P) [ f ]
    ⋀-eval : ∀ {X Y} {P : Predicate (P.prod X Y)} → ((⋀ P) [ P.p₁ ]) ⊑ P
    ⋀-lambda : ∀ {X Y} {P : Predicate X} {Q : Predicate (P.prod X Y)} → P [ P.p₁ ] ⊑ Q → P ⊑ ⋀ Q

    -- FIXME: this is experimental
    ⋁        : ∀ {X} (I : Set 0ℓ) → (I → Predicate X) → Predicate X
    ⋁-isJoin : ∀ {X} → IsBigJoin (⊑-isPreorder {X}) 0ℓ ⋁
    []-⋁     : ∀ {X Y I} {P : I → Predicate Y} {f : X 𝒞.⇒ Y} → (⋁ I P [ f ]) ⊑ ⋁ I (λ i → P i [ f ])

  -- Derived properties of meets
  _[&&]_ : ∀ {X Y} → Predicate X → Predicate Y → Predicate (P.prod X Y)
  P [&&] Q = (P [ P.p₁ ]) && (Q [ P.p₂ ])

  [&&]-p₁ : ∀ {X Y}{P : Predicate X}{Q : Predicate Y} → (P [&&] Q) ⊑ P [ P.p₁ ]
  [&&]-p₁ = &&-isMeet .IsMeet.π₁

  [&&]-p₂ : ∀ {X Y}{P : Predicate X}{Q : Predicate Y} → (P [&&] Q) ⊑ Q [ P.p₂ ]
  [&&]-p₂ = &&-isMeet .IsMeet.π₂

  [&&]-pair : ∀ {X Y Z}{P : Predicate X}{Q : Predicate Y}{R : Predicate Z}
              {f : X 𝒞.⇒ Y} {g : X 𝒞.⇒ Z} →
              P ⊑ Q [ f ] →
              P ⊑ R [ g ] →
              P ⊑ (Q [&&] R) [ P.pair f g ]
  [&&]-pair {X} {Y} {Z} {P} {Q} {R} {f} {g} ϕ ψ = begin
      P
    ≤⟨ &&-isMeet .IsMeet.⟨_,_⟩ ϕ ψ ⟩
      (Q [ f ]) && (R [ g ])
    ≤⟨ IsMeet.mono &&-isMeet ([]-cong (𝒞.≈-sym (P.pair-p₁ f g))) ([]-cong (𝒞.≈-sym (P.pair-p₂ f g))) ⟩
      (Q [ P.p₁ 𝒞.∘ P.pair f g ]) && (R [ P.p₂ 𝒞.∘ P.pair f g  ])
    ≤⟨ IsMeet.mono &&-isMeet ([]-comp⁻¹ _ _) ([]-comp⁻¹ _ _) ⟩
      (Q [ P.p₁ ] [ P.pair f g ]) && (R [ P.p₂ ]  [ P.pair f g  ])
    ≤⟨ []-&& ⟩
      (Q [&&] R) [ P.pair f g ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder

  --
  []-++⁻¹ : ∀ {X Y} {P Q : Predicate Y} {f : X 𝒞.⇒ Y} → ((P [ f ]) ++ (Q [ f ])) ⊑ ((P ++ Q) [ f ])
  []-++⁻¹ = ++-isJoin .IsJoin.[_,_] ((++-isJoin .IsJoin.inl) [ _ ]m) ((++-isJoin .IsJoin.inr) [ _ ]m)

  -- Derived properties of products
  ⋀-[]⁻¹ : ∀ {X X' Y} {P : Predicate (P.prod X Y)} {f : X' 𝒞.⇒ X} → (⋀ P) [ f ] ⊑ (⋀ (P [ P.prod-m f (𝒞.id _) ]))
  ⋀-[]⁻¹ {X} {X'} {Y} {P} {f} = ⋀-lambda Φ
    where
      Φ : ((⋀ P [ f ]) [ P.p₁ ]) ⊑ (P [ P.prod-m f (𝒞.id Y) ])
      Φ = begin
            (⋀ P [ f ]) [ P.p₁ ]
           ≤⟨ []-comp _ _ ⟩
            ⋀ P [ f 𝒞.∘ P.p₁ ]
           ≤⟨ []-cong (𝒞.≈-sym (P.pair-p₁ _ _)) ⟩
            ⋀ P [ P.p₁ 𝒞.∘ P.prod-m f (𝒞.id Y) ]
           ≤⟨ []-comp⁻¹ _ _ ⟩
            ⋀ P [ P.p₁ ] [ P.prod-m f (𝒞.id Y) ]
           ≤⟨ ⋀-eval [ _ ]m ⟩
            P [ P.prod-m f (𝒞.id Y) ]
       ∎
       where open ≤-Reasoning ⊑-isPreorder

record ClosureOp (S : PredicateSystem) : Set (suc (o ⊔ m ⊔ e)) where
  open PredicateSystem S
  field
    𝐂           : ∀ {X} → Predicate X → Predicate X
    𝐂-isClosure : ∀ {X} → IsClosureOp (⊑-isPreorder {X}) 𝐂
    𝐂-[]        : ∀ {X Y} {P : Predicate Y} {f : X 𝒞.⇒ Y} → 𝐂 (P [ f ]) ⊑ (𝐂 P [ f ])
    𝐂-[]⁻¹      : ∀ {X Y} {P : Predicate Y} {f : X 𝒞.⇒ Y} → (𝐂 P [ f ]) ⊑ 𝐂 (P [ f ])
    𝐂-strong    : ∀ {X} {P Q : Predicate X} → (𝐂 P && Q) ⊑ 𝐂 (P && Q)

  𝐂-monoidal : ∀ {X} {P Q : Predicate X} → (𝐂 P && 𝐂 Q) ⊑ 𝐂 (P && Q)
  𝐂-monoidal {X} {P} {Q} = begin
      𝐂 P && 𝐂 Q
    ≤⟨ 𝐂-strong ⟩
      𝐂 (P && 𝐂 Q)
    ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsMeet.comm &&-isMeet) ⟩
      𝐂 (𝐂 Q && P)
    ≤⟨ 𝐂-isClosure .IsClosureOp.mono 𝐂-strong ⟩
      𝐂 (𝐂 (Q && P))
    ≤⟨ 𝐂-isClosure .IsClosureOp.closed ⟩
      𝐂 (Q && P)
    ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsMeet.comm &&-isMeet) ⟩
      𝐂 (P && Q)
    ∎
    where open ≤-Reasoning ⊑-isPreorder

module exponentials (S : PredicateSystem) (E : HasExponentials 𝒞 P) where

  open PredicateSystem S
  private
    module E = HasExponentials E

  _[=>]_ : ∀ {X Y} → Predicate X → Predicate Y → Predicate (E.exp X Y)
  P [=>] Q = ⋀ ((P [ P.p₂ ]) ==> (Q [ E.eval ]))

  [=>]-lambda : ∀ {X Y Z} {P : Predicate X} {Q : Predicate Y} {R : Predicate Z} {f : P.prod X Y 𝒞.⇒ Z} →
                (P [&&] Q) ⊑ R [ f ] → P ⊑ (Q [=>] R) [ E.lambda f ]
  [=>]-lambda {X} {Y} {Z} {P} {Q} {R} {f} ϕ = begin
      P
    ≤⟨ ⋀-lambda Ψ ⟩
      ⋀ (((Q [ P.p₂ ]) ==> (R [ E.eval ])) [ P.prod-m (E.lambda f) (𝒞.id _) ])
    ≤⟨ ⋀-[] ⟩
      ((Q [=>] R) [ E.lambda f ])
    ∎
    where
      Ψ : (P [ P.p₁ ]) ⊑ (((Q [ P.p₂ ]) ==> (R [ E.eval ])) [ P.prod-m (E.lambda f) (𝒞.id Y) ])
      Ψ = begin
            P [ P.p₁ ]
          ≤⟨ ==>-residual .IsResidual.lambda ϕ ⟩
            (Q [ P.p₂ ]) ==> (R [ f ])
          ≤⟨ IsResidual.-∙-mono ==>-residual ([]-cong 𝒞.id-left) (⊑-isPreorder .IsPreorder.refl) ⟩
            (Q [ 𝒞.id Y 𝒞.∘ P.p₂ ]) ==> (R [ f ])
          ≤⟨ IsResidual.-∙-mono ==>-residual ([]-cong (P.pair-p₂ _ _)) ([]-cong (𝒞.≈-sym (E.eval-lambda _))) ⟩
            (Q [ P.p₂ 𝒞.∘ P.prod-m (E.lambda f) (𝒞.id Y) ]) ==> (R [ E.eval 𝒞.∘ P.prod-m (E.lambda f) (𝒞.id Y) ])
          ≤⟨ IsResidual.-∙-mono ==>-residual ([]-comp _ _) ([]-comp⁻¹ _ _) ⟩
            (Q [ P.p₂ ] [ P.prod-m (E.lambda f) (𝒞.id Y) ]) ==> (R [ E.eval ] [ P.prod-m (E.lambda f) (𝒞.id Y) ])
          ≤⟨ []-==> ⟩
            ((Q [ P.p₂ ]) ==> (R [ E.eval ])) [ P.prod-m (E.lambda f) (𝒞.id Y) ]
          ∎
          where open ≤-Reasoning ⊑-isPreorder

      open ≤-Reasoning ⊑-isPreorder

  [=>]-eval : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} →
              ((P [=>] Q) [&&] P) ⊑ Q [ E.eval ]
  [=>]-eval {X} {Y} {P} {Q} = begin
      (⋀ ((P [ P.p₂ ]) ==> (Q [ E.eval ])) [ P.p₁ ]) && (P [ P.p₂ ])
    ≤⟨ IsMeet.mono &&-isMeet ⋀-eval (⊑-isPreorder .IsPreorder.refl) ⟩
      ((P [ P.p₂ ]) ==> (Q [ E.eval ])) && (P [ P.p₂ ])
    ≤⟨ ==>-residual .IsResidual.eval ⟩
      Q [ E.eval ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder

  [=>]-mono : ∀ {X Y} {P P' : Predicate X} {Q Q' : Predicate Y} →
              P' ⊑ P →
              Q ⊑ Q' →
              (P [=>] Q) ⊑ (P' [=>] Q')
  [=>]-mono {X} {Y} {P} {P'} {Q} {Q'} ϕ ψ = ⋀-lambda (==>-residual .IsResidual.lambda (begin
      (⋀ ((P [ P.p₂ ]) ==> (Q [ E.eval ])) [ P.p₁ ]) && (P' [ P.p₂ ])
    ≤⟨ IsMeet.mono &&-isMeet ⋀-eval (ϕ [ _ ]m) ⟩
      ((P [ P.p₂ ]) ==> (Q [ E.eval ])) && (P [ P.p₂ ])
    ≤⟨ ==>-residual .IsResidual.eval ⟩
      Q [ E.eval ]
    ≤⟨ ψ [ _ ]m ⟩
      Q' [ E.eval ]
    ∎))
    where open ≤-Reasoning ⊑-isPreorder

--   [=>]-reindex :
