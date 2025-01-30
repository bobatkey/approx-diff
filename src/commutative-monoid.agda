{-# OPTIONS --prop --postfix-projections --safe #-}

module commutative-monoid o where

open import Level
open import Data.Product using (_,_; proj₁; proj₂)
open import prop
open import prop-setoid
  using (Setoid; IsEquivalence; idS; _∘S_; ⊗-setoid; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≃s_; ≃m-isEquivalence to ≃s-isEquivalence)
open import categories

------------------------------------------------------------------------------
-- Commutative Monoid structure on setoids
--
record CommutativeMonoid (A : Setoid o o) : Set o where
  open Setoid A
  field
    ε   : Carrier
    _+_ : Carrier → Carrier → Carrier
    +-cong  : ∀ {x₁ x₂ y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → (x₁ + y₁) ≈ (x₂ + y₂)
    +-lunit : ∀ {x} → (ε + x) ≈ x
    +-assoc : ∀ {x y z} → ((x + y) + z) ≈ (x + (y + z))
    +-comm  : ∀ {x y} → (x + y) ≈ (y + x)

record _=[_]>_ {A B}(X : CommutativeMonoid A)(f : A ⇒s B)(Y : CommutativeMonoid B) : Prop o where
  private
    module X = CommutativeMonoid X
    module Y = CommutativeMonoid Y
  open _⇒s_ f
  open Setoid B
  field
    preserve-ε : func X.ε ≈ Y.ε
    preserve-+ : ∀ {x₁ x₂} → func (x₁ X.+ x₂) ≈ (func x₁ Y.+ func x₂)
open _=[_]>_

module _ where

  open CommutativeMonoid

  _⊗_ : ∀ {A B} → CommutativeMonoid A → CommutativeMonoid B → CommutativeMonoid (⊗-setoid A B)
  (X ⊗ Y) .ε = X .ε , Y .ε
  (X ⊗ Y) ._+_ (x₁ , y₁) (x₂ , y₂) = X ._+_ x₁ x₂ , Y ._+_ y₁ y₂
  (X ⊗ Y) .+-cong (x₁≈x₂ , y₁≈y₂) (x'₁≈x'₂ , y'₁≈y'₂) =
     X .+-cong x₁≈x₂ x'₁≈x'₂ , Y .+-cong y₁≈y₂ y'₁≈y'₂
  (X ⊗ Y) .+-lunit = X .+-lunit , Y .+-lunit
  (X ⊗ Y) .+-assoc = X .+-assoc , Y .+-assoc
  (X ⊗ Y) .+-comm = X .+-comm , Y .+-comm

------------------------------------------------------------------------------
-- The category of commutative monoids.
record Obj : Set (suc o) where
  no-eta-equality
  field
    carrier    : Setoid o o
    commMonoid : CommutativeMonoid carrier
  open Setoid carrier public
  open CommutativeMonoid commMonoid public

record _⇒_ (X Y : Obj) : Set o where
  open Obj
  field
    function : X .carrier ⇒s Y .carrier
    cmFunc   : X .commMonoid =[ function ]> Y .commMonoid
  open _=[_]>_ cmFunc public
open _⇒_

_≃_ : ∀ {X Y} (f g : X ⇒ Y) → Prop o
f ≃ g = f .function ≃s g .function

open IsEquivalence

≃-isEquivalence : ∀ {X Y} → IsEquivalence (_≃_ {X} {Y})
≃-isEquivalence .refl = ≃s-isEquivalence .refl
≃-isEquivalence .sym = ≃s-isEquivalence .sym
≃-isEquivalence .trans = ≃s-isEquivalence .trans

module _ where
  open Obj
  open _⇒s_

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

cat : Category (suc o) o o
cat .Category.obj = Obj
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
module _ where

  open Obj
  open import setoid-cat
  open import functor

  open Functor

  toSetoid : Functor cat (SetoidCat o o)
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
module _ {X Y : Obj} where
  open _⇒s_
  open _≃s_

  private
    module X = Obj X
    module Y = Obj Y

  εm : X ⇒ Y
  εm .function .func x = Y.ε
  εm .function .func-resp-≈ x = Y.refl
  εm .cmFunc .preserve-ε = Y.refl
  εm .cmFunc .preserve-+ = Y.sym Y.+-lunit

  _+m_ : X ⇒ Y → X ⇒ Y → X ⇒ Y
  _+m_ f g .function .func x = f .function .func x Y.+ g .function .func x
  _+m_ f g .function .func-resp-≈ x₁≈x₂ = Y.+-cong (f .function .func-resp-≈ x₁≈x₂) (g .function .func-resp-≈ x₁≈x₂)
  _+m_ f g .cmFunc .preserve-ε = Y.trans (Y.+-cong (f .cmFunc .preserve-ε) (g .cmFunc .preserve-ε)) Y.+-lunit
  (f +m g) .cmFunc .preserve-+ {x₁} {x₂} =
    begin
      f' (x₁ X.+ x₂) Y.+ g' (x₁ X.+ x₂)
    ≈⟨ Y.+-cong (f .cmFunc .preserve-+) (g .cmFunc .preserve-+) ⟩
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
          f' = f .function .func
          g' = g. function .func

module _ (X Y : Obj) where
  open _⇒s_
  open _≃s_

  private
    module X = Obj X
    module Y = Obj Y

  homCM : CommutativeMonoid (Category.hom-setoid cat X Y)
  homCM .CommutativeMonoid.ε = εm
  homCM .CommutativeMonoid._+_ = _+m_
  homCM .CommutativeMonoid.+-cong f₁≈f₂ g₁≈g₂ .func-eq x₁≈x₂ =
    Y.+-cong (f₁≈f₂ .func-eq x₁≈x₂) (g₁≈g₂ .func-eq x₁≈x₂)
  homCM .CommutativeMonoid.+-lunit {f} .func-eq x₁≈x₂ =
    Y.trans Y.+-lunit (f .function .func-resp-≈ x₁≈x₂)
  homCM .CommutativeMonoid.+-assoc {f} {g} {h} .func-eq x₁≈x₂ =
    Y.trans Y.+-assoc
      (Y.+-cong (f .function .func-resp-≈ x₁≈x₂)
                (Y.+-cong (g .function .func-resp-≈ x₁≈x₂)
                          (h .function .func-resp-≈ x₁≈x₂)))
  homCM .CommutativeMonoid.+-comm {f} {g} .func-eq x₁≈x₂ =
    Y.trans Y.+-comm (Y.+-cong (g. function .func-resp-≈ x₁≈x₂)
                               (f .function .func-resp-≈ x₁≈x₂))

module _ where

  open Obj
  open _⇒s_
  open _≃s_

  comp-bilinear₁ : ∀ {X Y Z} (f₁ f₂ : Y ⇒ Z) (g : X ⇒ Y) →
                   ((f₁ +m f₂) ∘ g) ≃ ((f₁ ∘ g) +m (f₂ ∘ g))
  comp-bilinear₁ {Z = Z} f₁ f₂ g .func-eq x₁≈x₂ =
    Z .+-cong (f₁ .function .func-resp-≈ (g .function .func-resp-≈ x₁≈x₂))
              (f₂ .function .func-resp-≈ (g .function .func-resp-≈ x₁≈x₂))

  comp-bilinear₂ : ∀ {X Y Z} (f : Y ⇒ Z) (g₁ g₂ : X ⇒ Y) →
                   (f ∘ (g₁ +m g₂)) ≃ ((f ∘ g₁) +m (f ∘ g₂))
  comp-bilinear₂ {Z = Z} f g₁ g₂ .func-eq x₁≈x₂ =
    Z .trans
       (f .cmFunc .preserve-+)
       (Z .+-cong (f .function .func-resp-≈ (g₁ .function .func-resp-≈ x₁≈x₂))
                  (f .function .func-resp-≈ (g₂ .function .func-resp-≈ x₁≈x₂)))

------------------------------------------------------------------------------
-- Big Products
module _ where

  open import fam
  open import setoid-cat

  open Obj
  open Fam
  open CommutativeMonoid
  open ΠS-Carrier
  open HasSetoidProducts

  ΠCM : (A : Setoid o o) → Fam A cat → Obj
  ΠCM A F .carrier = ΠS A (changeCat A toSetoid F)
  ΠCM A F .commMonoid .ε .Π-func a = F .fm a .commMonoid .ε
  ΠCM A F .commMonoid .ε .Π-eq e = F .subst e .cmFunc .preserve-ε
  ΠCM A F .commMonoid ._+_ f₁ f₂ .Π-func a = F .fm a .commMonoid ._+_ (f₁ .Π-func a) (f₂ .Π-func a)
  ΠCM A F .commMonoid ._+_ f₁ f₂ .Π-eq {a₁} {a₂} a₁≈a₂ =
    begin
      F .subst a₁≈a₂ .function ._⇒s_.func (F .fm a₁ .commMonoid ._+_ (f₁ .Π-func a₁) (f₂ .Π-func a₁))
    ≈⟨ F .subst a₁≈a₂ .cmFunc .preserve-+ ⟩
      F .fm a₂ .commMonoid ._+_ (F .subst a₁≈a₂ .function ._⇒s_.func (f₁ .Π-func a₁)) (F .subst a₁≈a₂ .function ._⇒s_.func (f₂ .Π-func a₁))
    ≈⟨ F .fm a₂ .commMonoid .+-cong (f₁ .Π-eq a₁≈a₂) (f₂ .Π-eq a₁≈a₂) ⟩
      F .fm a₂ .commMonoid ._+_ (f₁ .Π-func a₂) (f₂ .Π-func a₂)
    ∎ where open ≈-Reasoning (F .fm a₂ .carrier .Setoid.isEquivalence)
  ΠCM A F .commMonoid .+-cong f₁≈f₂ g₁≈g₂ a =
    F .fm a .commMonoid .+-cong (f₁≈f₂ a) (g₁≈g₂ a)
  ΠCM A F .commMonoid .+-lunit a = F .fm a .commMonoid .+-lunit
  ΠCM A F .commMonoid .+-assoc a = F .fm a .commMonoid .+-assoc
  ΠCM A F .commMonoid .+-comm a = F .fm a .commMonoid .+-comm

  evalΠCM : ∀ {A} P (a : A .Setoid.Carrier) → ΠCM A P ⇒ P .fm a
  evalΠCM P a .function = Setoid-BigProducts .evalΠ (changeCat _ toSetoid P) a
  evalΠCM P a .cmFunc .preserve-ε = P .fm a .carrier .Setoid.refl
  evalΠCM P a .cmFunc .preserve-+ = P .fm a .carrier .Setoid.refl

  lambdaΠCM : ∀ {A} (X : Obj) (P : Fam A cat) →
              (constantFam A cat X ⇒f P) → (X ⇒ ΠCM A P)
  lambdaΠCM {A} X P f .function =
    Setoid-BigProducts .lambdaΠ (X .carrier) (changeCat _ toSetoid P)
      (changeCatF A toSetoid f ∘f preserveConst⁻¹ A toSetoid X)
  lambdaΠCM X P f .cmFunc .preserve-ε a = f ._⇒f_.transf a .cmFunc .preserve-ε
  lambdaΠCM X P f .cmFunc .preserve-+ a = f ._⇒f_.transf a .cmFunc .preserve-+

  bigProd : HasSetoidProducts o o cat
  bigProd .Π = ΠCM
  bigProd .lambdaΠ = lambdaΠCM
  bigProd .lambdaΠ-cong f₁≈f₂ =
    Setoid-BigProducts .lambdaΠ-cong (∘f-cong (changeCatF-cong _ toSetoid f₁≈f₂) (≃f-isEquivalence .refl))
  bigProd .evalΠ = evalΠCM
  bigProd .evalΠ-cong a₁≈a₂ = Setoid-BigProducts .evalΠ-cong a₁≈a₂
  bigProd .lambda-eval {A} {P} {x} {f} a ._≃s_.func-eq =
    f ._⇒f_.transf a .function ._⇒s_.func-resp-≈
  bigProd .lambda-ext {f = f} ._≃s_.func-eq =
    f .function ._⇒s_.func-resp-≈

------------------------------------------------------------------------------
-- Tensor products and symmetric monoidal closed structure (FIXME)

------------------------------------------------------------------------------
-- Biproducts
module _ where
  open Obj

  _⊕_ : Obj → Obj → Obj
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

  products : HasProducts cat
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

  -- FIXME: any additive category with products has biproducts
