{-# OPTIONS --prop --postfix-projections --safe #-}

module predicate-system where

open import Level using (suc; _⊔_)
open import basics using (IsPreorder; IsTop; IsMeet; IsResidual; monoidOfMeet)
open import categories using (Category; HasProducts; HasCoproducts)

record PredicateSystem {o m e} (𝒟 : Category o m e) (P : HasProducts 𝒟) (CP : HasCoproducts 𝒟) : Set (suc (suc (o ⊔ m ⊔ e))) where
  private
    module 𝒟 = Category 𝒟
    module P = HasProducts P
    module CP = HasCoproducts CP
  field
    Predicate : 𝒟.obj → Set (suc o ⊔ suc m ⊔ suc e)
    _⊑_   : ∀ {X : 𝒟.obj} → Predicate X → Predicate X → Prop (o ⊔ m ⊔ e)

  infix 2 _⊑_
  field
    _[_]   : ∀ {X Y} → Predicate Y → X 𝒟.⇒ Y → Predicate X
    _⟨_⟩   : ∀ {X Y} → Predicate X → X 𝒟.⇒ Y → Predicate Y

  field
    TT    : ∀ {X} → Predicate X
    _&&_  : ∀ {X} → Predicate X → Predicate X → Predicate X
    _++_  : ∀ {X Y} → Predicate X → Predicate Y → Predicate (CP.coprod X Y)
    _==>_ : ∀ {X} → Predicate X → Predicate X → Predicate X
    ⋀     : ∀ {X Y} → Predicate (P.prod X Y) → Predicate X

    ⊑-isPreorder : ∀ {X} → IsPreorder (_⊑_ {X})

    _[_]m     : ∀ {X Y} {P Q : Predicate Y} → P ⊑ Q → (f : X 𝒟.⇒ Y) → (P [ f ]) ⊑ (Q [ f ])
    []-cong   : ∀ {X Y} {P : Predicate Y}{f₁ f₂ : X 𝒟.⇒ Y} → f₁ 𝒟.≈ f₂ → (P [ f₁ ]) ⊑ (P [ f₂ ])
    []-id     : ∀ {X} {P : Predicate X} → P ⊑ (P [ 𝒟.id _ ])
    []-id⁻¹   : ∀ {X} {P : Predicate X} → (P [ 𝒟.id _ ]) ⊑ P
    []-comp   : ∀ {X Y Z} {P : Predicate Z} (f : Y 𝒟.⇒ Z) (g : X 𝒟.⇒ Y) → ((P [ f ]) [ g ]) ⊑ (P [ f 𝒟.∘ g ])
    []-comp⁻¹ : ∀ {X Y Z} {P : Predicate Z} (f : Y 𝒟.⇒ Z) (g : X 𝒟.⇒ Y) → (P [ f 𝒟.∘ g ]) ⊑ ((P [ f ]) [ g ])

    _⟨_⟩m     : ∀ {X Y} {P Q : Predicate X} → P ⊑ Q → (f : X 𝒟.⇒ Y) → (P ⟨ f ⟩) ⊑ (Q ⟨ f ⟩)

    adjoint₁ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} {f : X 𝒟.⇒ Y} → P ⟨ f ⟩ ⊑ Q → P ⊑ Q [ f ]
    adjoint₂ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} {f : X 𝒟.⇒ Y} → P ⊑ Q [ f ] → P ⟨ f ⟩ ⊑ Q

  unit : ∀ {X Y} {P : Predicate X} (f : X 𝒟.⇒ Y) → P ⊑ P ⟨ f ⟩ [ f ]
  unit f = adjoint₁ (IsPreorder.refl ⊑-isPreorder)

  counit : ∀ {X Y} {P : Predicate Y} (f : X 𝒟.⇒ Y) → P [ f ] ⟨ f ⟩ ⊑ P
  counit f = adjoint₂ (IsPreorder.refl ⊑-isPreorder)

  field
    TT-isTop  : ∀ {X} → IsTop ⊑-isPreorder (TT {X})

    &&-isMeet : ∀ {X} → IsMeet ⊑-isPreorder (_&&_ {X})
    []-&&     : ∀ {X Y} {P Q : Predicate Y} {f : X 𝒟.⇒ Y} → ((P [ f ]) && (Q [ f ])) ⊑ ((P && Q) [ f ])

    ==>-residual : ∀ {X} → IsResidual ⊑-isPreorder (monoidOfMeet _ &&-isMeet TT-isTop) (_==>_ {X})
    []-==> : ∀ {X Y}{P Q : Predicate Y}{f : X 𝒟.⇒ Y} → ((P [ f ]) ==> (Q [ f ])) ⊑ (P ==> Q) [ f ]

    ++-in₁ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} → P ⊑ (P ++ Q) [ CP.in₁ ]
    ++-in₂ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} → Q ⊑ (P ++ Q) [ CP.in₂ ]
    ++-copair : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} {R : Predicate (CP.coprod X Y)} →
                P ⊑ R [ CP.in₁ ] → Q ⊑ R [ CP.in₂ ] → (P ++ Q) ⊑ R

    ⋀-[] : ∀ {X X' Y} {P : Predicate (P.prod X Y)} {f : X' 𝒟.⇒ X} → (⋀ (P [ P.prod-m f (𝒟.id _) ])) ⊑ (⋀ P) [ f ]
    ⋀-eval : ∀ {X Y} {P : Predicate (P.prod X Y)} → ((⋀ P) [ P.p₁ ]) ⊑ P
    ⋀-lambda : ∀ {X Y} {P : Predicate X} {Q : Predicate (P.prod X Y)} → P [ P.p₁ ] ⊑ Q → P ⊑ ⋀ Q
