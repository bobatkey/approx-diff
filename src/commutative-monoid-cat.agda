{-# OPTIONS --prop --postfix-projections --safe #-}

module commutative-monoid-cat where

open import Level
open import prop
open import prop-setoid
  using (Setoid; IsEquivalence; idS; _∘S_; ⊗-setoid; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≃s_; ≃m-isEquivalence to ≃s-isEquivalence)
open import categories
open import commutative-monoid
open import cmon-enriched

------------------------------------------------------------------------------
-- The category of commutative monoids.
module _ {o e} where
  record Obj : Set (suc o ⊔ suc e) where
    no-eta-equality
    field
      carrier    : Setoid o e
      commMonoid : CommutativeMonoid carrier
    open Setoid carrier public
    open CommutativeMonoid commMonoid public

  record _⇒_ (X Y : Obj) : Set (o ⊔ e) where
    open Obj
    field
      function : X .carrier ⇒s Y .carrier
      cmFunc   : X .commMonoid =[ function ]> Y .commMonoid
    open _⇒s_ function public
    open _=[_]>_ cmFunc public
  open _⇒_

  _≃_ : ∀ {X Y} (f g : X ⇒ Y) → Prop (o ⊔ e)
  f ≃ g = f .function ≃s g .function

  open IsEquivalence

  ≃-isEquivalence : ∀ {X Y} → IsEquivalence (_≃_ {X} {Y})
  ≃-isEquivalence .refl = ≃s-isEquivalence .refl
  ≃-isEquivalence .sym = ≃s-isEquivalence .sym
  ≃-isEquivalence .trans = ≃s-isEquivalence .trans

  module _ where
    open Obj
    open _⇒s_
    open _=[_]>_

    id : (X : Obj) → X ⇒ X
    id X .function = idS (X .carrier)
    id X .cmFunc .preserve-ε = X .refl
    id X .cmFunc .preserve-+ = X .refl

    _∘_ : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
    (f ∘ g) .function = f .function ∘S g .function
    _∘_ {Z = Z} f g .cmFunc .preserve-ε =
      Z .trans (f .function .func-resp-≈ (g .preserve-ε)) (f .preserve-ε)
    _∘_ {Z = Z} f g .cmFunc .preserve-+ =
      Z .trans (f .function .func-resp-≈ (g .preserve-+)) (f .preserve-+)

module _ o e where

  cat : Category (suc o ⊔ suc e) (o ⊔ e) (o ⊔ e)
  cat .Category.obj = Obj {o} {e}
  cat .Category._⇒_ = _⇒_
  cat .Category._≈_ = _≃_
  cat .Category.isEquiv = ≃-isEquivalence
  cat .Category.id = id
  cat .Category._∘_ = _∘_
  cat .Category.∘-cong = prop-setoid.∘S-cong
  cat .Category.id-left = prop-setoid.id-left
  cat .Category.id-right = prop-setoid.id-right
  cat .Category.assoc _ _ _ = prop-setoid.assoc _ _ _

------------------------------------------------------------------------------
-- Forgetful functor to Setoids
module _ {o e} where

  open Obj
  open import setoid-cat hiding (Π)
  open import functor
  open IsEquivalence

  open Functor
  open _⇒_

  toSetoid : Functor (cat o e) (SetoidCat o e)
  toSetoid .fobj X = X .carrier
  toSetoid .fmor f = f .function
  toSetoid .fmor-cong eq = eq
  toSetoid .fmor-id = ≃s-isEquivalence .refl
  toSetoid .fmor-comp _ _ = ≃s-isEquivalence .refl

-- FIXME: free commutative monoid functor

------------------------------------------------------------------------------
-- Additive structure on morphisms, so that every homset is a
-- commutative monoid, and composition is a commutative monoid
-- morphism.
module _ {o e} {X Y : Obj {o} {e}} where
  open _⇒s_
  open _≃s_
  open _⇒_
  open _=[_]>_

  private
    module X = Obj X
    module Y = Obj Y

  εm : X ⇒ Y
  εm .function .func x = Y.ε
  εm .function .func-resp-≈ x = Y.refl
  εm .cmFunc .preserve-ε = Y.refl
  εm .cmFunc .preserve-+ = Y.sym Y.+-lunit

  _+m_ : X ⇒ Y → X ⇒ Y → X ⇒ Y
  _+m_ f g .function .func x = f .func x Y.+ g .func x
  _+m_ f g .function .func-resp-≈ x₁≈x₂ = Y.+-cong (f .func-resp-≈ x₁≈x₂) (g .func-resp-≈ x₁≈x₂)
  _+m_ f g .cmFunc .preserve-ε = Y.trans (Y.+-cong (f .preserve-ε) (g .preserve-ε)) Y.+-lunit
  (f +m g) .cmFunc .preserve-+ {x₁} {x₂} =
    begin
      f' (x₁ X.+ x₂) Y.+ g' (x₁ X.+ x₂)
    ≈⟨ Y.+-cong (f .preserve-+) (g .preserve-+) ⟩
      (f' x₁ Y.+ f' x₂) Y.+ (g' x₁ Y.+ g' x₂)
    ≈⟨ Y.+-assoc ⟩
      f' x₁ Y.+ (f' x₂ Y.+ (g' x₁ Y.+ g' x₂))
    ≈⟨ Y.+-cong Y.refl (Y.sym Y.+-assoc) ⟩
      f' x₁ Y.+ ((f' x₂ Y.+ g' x₁) Y.+ g' x₂)
    ≈⟨ Y.+-cong Y.refl (Y.+-cong Y.+-comm Y.refl) ⟩
      f' x₁ Y.+ ((g' x₁ Y.+ f' x₂) Y.+ g' x₂)
    ≈⟨ Y.+-cong Y.refl Y.+-assoc ⟩
      f' x₁ Y.+ (g' x₁ Y.+ (f' x₂ Y.+ g' x₂))
    ≈⟨ Y.sym Y.+-assoc ⟩
      (f' x₁ Y.+ g' x₁) Y.+ (f' x₂ Y.+ g' x₂)
    ∎
    where open ≈-Reasoning Y.isEquivalence
          f' = f .func
          g' = g .func

module _ {o e} (X Y : Obj {o} {e}) where
  open _⇒_
  open _⇒s_
  open _≃s_

  private
    module X = Obj X
    module Y = Obj Y

  homCM : CommutativeMonoid (Category.hom-setoid (cat o e) X Y)
  homCM .CommutativeMonoid.ε = εm
  homCM .CommutativeMonoid._+_ = _+m_
  homCM .CommutativeMonoid.+-cong f₁≈f₂ g₁≈g₂ .func-eq x₁≈x₂ =
    Y.+-cong (f₁≈f₂ .func-eq x₁≈x₂) (g₁≈g₂ .func-eq x₁≈x₂)
  homCM .CommutativeMonoid.+-lunit {f} .func-eq x₁≈x₂ =
    Y.trans Y.+-lunit (f .func-resp-≈ x₁≈x₂)
  homCM .CommutativeMonoid.+-assoc {f} {g} {h} .func-eq x₁≈x₂ =
    Y.trans Y.+-assoc
      (Y.+-cong (f .func-resp-≈ x₁≈x₂)
                (Y.+-cong (g .func-resp-≈ x₁≈x₂) (h .func-resp-≈ x₁≈x₂)))
  homCM .CommutativeMonoid.+-comm {f} {g} .func-eq x₁≈x₂ =
    Y.trans Y.+-comm (Y.+-cong (g .func-resp-≈ x₁≈x₂) (f .func-resp-≈ x₁≈x₂))

module _ {o e} where

  open Obj
  open _⇒s_
  open _≃s_
  open _⇒_
  open _=[_]>_

  comp-bilinear₁ : ∀ {X Y Z : Obj {o} {e}} (f₁ f₂ : Y ⇒ Z) (g : X ⇒ Y) →
                   ((f₁ +m f₂) ∘ g) ≃ ((f₁ ∘ g) +m (f₂ ∘ g))
  comp-bilinear₁ {Z = Z} f₁ f₂ g .func-eq x₁≈x₂ =
    Z .+-cong (f₁ .func-resp-≈ (g .func-resp-≈ x₁≈x₂))
              (f₂ .func-resp-≈ (g .func-resp-≈ x₁≈x₂))

  comp-bilinear₂ : ∀ {X Y Z : Obj {o} {e}} (f : Y ⇒ Z) (g₁ g₂ : X ⇒ Y) →
                   (f ∘ (g₁ +m g₂)) ≃ ((f ∘ g₁) +m (f ∘ g₂))
  comp-bilinear₂ {Z = Z} f g₁ g₂ .func-eq x₁≈x₂ =
    Z .trans
       (f .preserve-+)
       (Z .+-cong (f .func-resp-≈ (g₁ .func-resp-≈ x₁≈x₂))
                  (f .func-resp-≈ (g₂ .func-resp-≈ x₁≈x₂)))

  cmon-enriched : CMonEnriched (cat o e)
  cmon-enriched .CMonEnriched.homCM = homCM
  cmon-enriched .CMonEnriched.comp-bilinear₁ = comp-bilinear₁
  cmon-enriched .CMonEnriched.comp-bilinear₂ = comp-bilinear₂
  cmon-enriched .CMonEnriched.comp-bilinear-ε₁ {Z = Z} f .func-eq _ = Z .refl
  cmon-enriched .CMonEnriched.comp-bilinear-ε₂ f .func-eq _ = f .preserve-ε

------------------------------------------------------------------------------
-- Limits, inherited from Setoids
module _ {o m e} os (𝒟 : Category o m e) where
   open import functor renaming (id to NTid; ≃-isEquivalence to ≃NT-isEquivalence; _∘_ to _∘V_)
   open import setoid-cat

   private
     module 𝒟 = Category 𝒟

   open Functor
   open NatTrans
   open ≃-NatTrans
   open Obj
   open _⇒_
   open _=[_]>_
   open Π-Carrier
   open CommutativeMonoid
   open IsEquivalence
   open Limit
   open IsLimit

   ΠCM : Functor 𝒟 (cat (os ⊔ o ⊔ m) (os ⊔ o ⊔ m)) → Obj {os ⊔ o ⊔ m} {os ⊔ o ⊔ m}
   ΠCM F .carrier = Π os 𝒟 (toSetoid ∘F F)
   ΠCM F .commMonoid .ε .Π-func x = F .fobj x .ε
   ΠCM F .commMonoid .ε .Π-eq f = F .fmor f .preserve-ε
   ΠCM F .commMonoid ._+_ f₁ f₂ .Π-func x = F .fobj x ._+_ (f₁ .Π-func x) (f₂ .Π-func x)
   ΠCM F .commMonoid ._+_ f₁ f₂ .Π-eq {x} {y} f =
     begin
       F .fmor f .func (F .fobj x ._+_ (f₁ .Π-func x) (f₂ .Π-func x))
     ≈⟨ F .fmor f .preserve-+ ⟩
       F .fobj y ._+_ (F .fmor f .func (f₁ .Π-func x)) (F .fmor f .func (f₂ .Π-func x))
     ≈⟨ F .fobj y .+-cong (f₁ .Π-eq f) (f₂ .Π-eq f) ⟩
       F .fobj y ._+_ (f₁ .Π-func y) (f₂ .Π-func y)
     ∎ where open ≈-Reasoning (F .fobj y .isEquivalence)
   ΠCM F .commMonoid .+-cong f₁≈f₂ g₁≈g₂ a = F .fobj a .+-cong (f₁≈f₂ a) (g₁≈g₂ a)
   ΠCM F .commMonoid .+-lunit x = F .fobj x .+-lunit
   ΠCM F .commMonoid .+-assoc x = F .fobj x .+-assoc
   ΠCM F .commMonoid .+-comm x = F .fobj x .+-comm

   evalΠCM : ∀ F → NatTrans (constF 𝒟 (ΠCM F)) F
   evalΠCM F .transf x .function =
     Setoid-Limit os 𝒟 (toSetoid ∘F F) .cone .transf x
   evalΠCM F .transf x .cmFunc .preserve-ε = F .fobj x .refl
   evalΠCM F .transf x .cmFunc .preserve-+ = F .fobj x .refl
   evalΠCM F .natural = Setoid-Limit os 𝒟 (toSetoid ∘F F) .cone .natural

   lambdaΠCM : ∀ X (F : Functor 𝒟 (cat (os ⊔ o ⊔ m) (os ⊔ o ⊔ m))) →
               NatTrans (constF 𝒟 X) F → (X ⇒ ΠCM F)
   lambdaΠCM X F α .function =
     Setoid-Limit os 𝒟 (toSetoid ∘F F) .isLimit .lambda (X .carrier) ((NTid toSetoid ∘H α) ∘V constF-F toSetoid X)
   lambdaΠCM X F α .cmFunc .preserve-ε x = α .transf x .preserve-ε
   lambdaΠCM X F α .cmFunc .preserve-+ x = α .transf x .preserve-+

   limits : (D : Functor 𝒟 (cat (os ⊔ o ⊔ m) (os ⊔ o ⊔ m))) → Limit D
   limits D .apex = ΠCM D
   limits D .cone = evalΠCM D
   limits D .isLimit .lambda X = lambdaΠCM X D
   limits D .isLimit .lambda-cong {x} {α} {β} α≃β =
     Setoid-Limit os 𝒟 (toSetoid ∘F D) .isLimit .lambda-cong
       (∘NT-cong (∘H-cong (≃NT-isEquivalence .refl) α≃β) (≃NT-isEquivalence .refl))
   limits D .isLimit .lambda-eval α .transf-eq x ._≃s_.func-eq = α .transf x .func-resp-≈
   limits D .isLimit .lambda-ext f ._≃s_.func-eq = f .func-resp-≈

------------------------------------------------------------------------------
-- Tensor products and symmetric monoidal closed structure (FIXME)

------------------------------------------------------------------------------
-- Products. Special case of limits, but this is likely more efficient.
module _ {o e} where
  open Obj
  open _⇒_
  open _=[_]>_

  𝟙 : Obj {o} {e}
  𝟙 .carrier = prop-setoid.𝟙 {o} {e}
  𝟙 .commMonoid = 𝟙cm

  terminal : HasTerminal (cat o e)
  terminal .HasTerminal.witness = 𝟙
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .function = prop-setoid.to-𝟙
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .cmFunc .preserve-ε = tt
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .cmFunc .preserve-+ = tt
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext f ._≃s_.func-eq _ = tt

  _⊕_ : Obj {o} {e} → Obj → Obj
  (X ⊕ Y) .carrier = ⊗-setoid (X .carrier) (Y .carrier)
  (X ⊕ Y) .commMonoid = X .commMonoid ⊗ Y .commMonoid

  p₁ : ∀ {X Y} → (X ⊕ Y) ⇒ X
  p₁ .function = prop-setoid.project₁
  p₁ {X} {Y} .cmFunc .preserve-ε = X .refl
  p₁ {X} {Y} .cmFunc .preserve-+ = X .refl

  p₂ : ∀ {X Y} → (X ⊕ Y) ⇒ Y
  p₂ .function = prop-setoid.project₂
  p₂ {X} {Y} .cmFunc .preserve-ε = Y .refl
  p₂ {X} {Y} .cmFunc .preserve-+ = Y .refl

  pair : ∀ {X Y Z} → X ⇒ Y → X ⇒ Z → X ⇒ (Y ⊕ Z)
  pair f g .function = prop-setoid.pair (f .function) (g .function)
  pair f g .cmFunc .preserve-ε = f .cmFunc .preserve-ε , g .cmFunc .preserve-ε
  pair f g .cmFunc .preserve-+ = (f .cmFunc .preserve-+) , (g .cmFunc .preserve-+)

  open import setoid-cat

  products : HasProducts (cat o e)
  products .HasProducts.prod = _⊕_
  products .HasProducts.p₁ = p₁
  products .HasProducts.p₂ = p₂
  products .HasProducts.pair = pair
  products .HasProducts.pair-cong f₁≈f₂ g₁≈g₂ =
    Setoid-products _ _ .HasProducts.pair-cong f₁≈f₂ g₁≈g₂
  products .HasProducts.pair-p₁ f g =
    Setoid-products _ _ .HasProducts.pair-p₁ (f .function) (g .function)
  products .HasProducts.pair-p₂ f g =
    Setoid-products _ _ .HasProducts.pair-p₂ (f .function) (g .function)
  products .HasProducts.pair-ext f =
    Setoid-products _ _ .HasProducts.pair-ext (f .function)

  -- FIXME: and so we have all biproducts too
