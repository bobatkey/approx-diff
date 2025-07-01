{-# OPTIONS --prop --postfix-projections --safe #-}

module setoid-predicate {o e} where

open import Level using (suc; _⊔_)
open import Data.Product using (_,_)
open import prop using (_∧_; _,_; proj₁; proj₂; ⊤; tt; ∃; LiftP; lower; _∨_; inj₁; inj₂; lift)
open import basics using (IsPreorder; IsMeet; IsTop; IsResidual; monoidOfMeet; IsJoin)
open import prop-setoid
  using (idS; Setoid; IsEquivalence; _∘S_; ∘S-cong;
         ⊗-setoid; project₁; project₂; pair; +-setoid; inject₁; inject₂;
         module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_; ≃m-isEquivalence to ≈s-isEquivalence)
open import setoid-cat using (SetoidCat; Setoid-products; Setoid-coproducts)

record Predicate (X : Setoid o e) : Set (suc (suc o ⊔ suc e)) where
  no-eta-equality
  private
    module X = Setoid X
  field
    pred   : X.Carrier → Prop (o ⊔ e)
    pred-≃ : ∀ {x₁ x₂} → x₁ X.≈ x₂ → pred x₁ → pred x₂

record _⊑_ {X : Setoid o e} (P Q : Predicate X) : Prop (suc o ⊔ suc e) where
  no-eta-equality
  field
    *⊑* : ∀ x → P .Predicate.pred x → Q .Predicate.pred x
open _⊑_

infix 2 _⊑_

⊑-refl : ∀ {X : Setoid o e} {P : Predicate X} → P ⊑ P
⊑-refl .*⊑* x p = p

⊑-trans : ∀ {X : Setoid o e} {P Q R : Predicate X} → P ⊑ Q → Q ⊑ R → P ⊑ R
⊑-trans P⊑Q Q⊑R .*⊑* x p = Q⊑R .*⊑* x (P⊑Q .*⊑* x p)

⊑-isPreorder : ∀ {X} → IsPreorder (_⊑_ {X})
⊑-isPreorder .IsPreorder.refl {P} = ⊑-refl {P = P}
⊑-isPreorder .IsPreorder.trans {P}{Q}{R} = ⊑-trans {P = P} {Q = Q} {R = R}

_&&_ : ∀ {X : Setoid o e} → Predicate X → Predicate X → Predicate X
(P && Q) .Predicate.pred x = (P .Predicate.pred x) ∧ (Q .Predicate.pred x)
(P && Q) .Predicate.pred-≃ x₁≈x₂ (p , q) = P .Predicate.pred-≃ x₁≈x₂ p , Q .Predicate.pred-≃ x₁≈x₂ q

&&-isMeet : ∀ {X} → IsMeet ⊑-isPreorder (_&&_ {X})
&&-isMeet .IsMeet.π₁ .*⊑* x = proj₁
&&-isMeet .IsMeet.π₂ .*⊑* x = proj₂
&&-isMeet .IsMeet.⟨_,_⟩ P⊑Q P⊑R .*⊑* x p = (P⊑Q .*⊑* x p) , (P⊑R .*⊑* x p)

open _≈s_
open _⇒s_

_[_] : ∀ {X Y : Setoid o e} → Predicate Y → X ⇒s Y → Predicate X
(P [ f ]) .Predicate.pred x = P .Predicate.pred (f ._⇒s_.func x)
(P [ f ]) .Predicate.pred-≃ x₁≈x₂ = P .Predicate.pred-≃ (f ._⇒s_.func-resp-≈ x₁≈x₂)

_⟨_⟩ : ∀ {X Y : Setoid o e} → Predicate X → X ⇒s Y → Predicate Y
_⟨_⟩ {X} {Y} P f .Predicate.pred y =
  ∃ (X .Setoid.Carrier) λ x → P .Predicate.pred x ∧ Y .Setoid._≈_ (f .func x) y
_⟨_⟩ {X} {Y} P f .Predicate.pred-≃ {y₁} {y₂} y₁≈y₂ (x , p , e) =
  x , p , Y .Setoid.trans e y₁≈y₂

adjoint₁ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} {f : X ⇒s Y} →
           P ⟨ f ⟩ ⊑ Q → P ⊑ Q [ f ]
adjoint₁ {X} {Y} {f = f} Φ .*⊑* x p = Φ .*⊑* (f .func x) (x , p , Y .Setoid.refl)

adjoint₂ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} {f : X ⇒s Y} →
           P ⊑ Q [ f ] → P ⟨ f ⟩ ⊑ Q
adjoint₂ {X} {Y} {P} {Q} {f} Φ .*⊑* y (x , p , e) =
  Q .Predicate.pred-≃ e (Φ .*⊑* x p)

_[_]m : ∀ {X Y : Setoid o e} {P Q : Predicate Y} → P ⊑ Q → (f : X ⇒s Y) → P [ f ] ⊑ Q [ f ]
(P⊑Q [ f ]m) .*⊑* x = P⊑Q .*⊑* (f ._⇒s_.func x)

_⟨_⟩m : ∀ {X Y : Setoid o e} {P Q : Predicate X} → P ⊑ Q → (f : X ⇒s Y) → P ⟨ f ⟩ ⊑ Q ⟨ f ⟩
(P⊑Q ⟨ f ⟩m) .*⊑* y (x , p , e) = x , P⊑Q .*⊑* x p , e

[]-cong : ∀ {X Y : Setoid o e}{P : Predicate Y}{f₁ f₂ : X ⇒s Y} → f₁ ≈s f₂ → P [ f₁ ] ⊑ P [ f₂ ]
[]-cong {X}{P = P} f₁≈f₂ .*⊑* x p = P .Predicate.pred-≃ (f₁≈f₂ .func-eq (X .Setoid.refl)) p

[]-id : ∀ {X : Setoid o e} {P : Predicate X} → P ⊑ P [ idS X ]
[]-id .*⊑* x p = p

[]-id⁻¹ : ∀ {X : Setoid o e} {P : Predicate X} → P [ idS X ] ⊑ P
[]-id⁻¹ .*⊑* x p = p

[]-comp : ∀ {X Y Z : Setoid o e} {P : Predicate Z} (f : Y ⇒s Z) (g : X ⇒s Y) →
          (P [ f ]) [ g ] ⊑ P [ f ∘S g ]
[]-comp f g .*⊑* x p = p

[]-comp⁻¹ : ∀ {X Y Z : Setoid o e} {P : Predicate Z} (f : Y ⇒s Z) (g : X ⇒s Y) →
          P [ f ∘S g ] ⊑ (P [ f ]) [ g ]
[]-comp⁻¹ f g .*⊑* x p = p

[]-&& : ∀ {X Y : Setoid o e} {P Q : Predicate Y} {f : X ⇒s Y} → ((P [ f ]) && (Q [ f ])) ⊑ (P && Q) [ f ]
[]-&& .*⊑* x ϕ = ϕ

-- Universal quantification
⋀ : ∀ {X Y : Setoid o e} → Predicate (⊗-setoid X Y) → Predicate X
⋀ P .Predicate.pred x = ∀ y → P .Predicate.pred (x , y)
⋀ {X} {Y} P .Predicate.pred-≃ x₁≈x₂ p y = P .Predicate.pred-≃ (x₁≈x₂ , Y .Setoid.refl) (p y)

_⊗m_ : ∀ {X X' Y Y' : Setoid o e} → X ⇒s X' → Y ⇒s Y' → (⊗-setoid X Y) ⇒s ⊗-setoid X' Y'
f ⊗m g = prop-setoid.pair (f ∘S project₁) (g ∘S project₂)

⋀-[] : ∀ {X X' Y : Setoid o e} {P : Predicate (⊗-setoid X Y)} {f : X' ⇒s X} →
       (⋀ (P [ f ⊗m (idS _) ])) ⊑ (⋀ P) [ f ]
⋀-[] .*⊑* x Φ y = Φ y

⋀-eval : ∀ {X Y : Setoid o e} {P : Predicate (⊗-setoid X Y)} → ((⋀ P) [ project₁ ]) ⊑ P
⋀-eval .*⊑* (x , y) z = z y

⋀-lambda : ∀ {X Y : Setoid o e} {P : Predicate X} {Q : Predicate (⊗-setoid X Y)} →
            P [ project₁ ] ⊑ Q →
            P ⊑ ⋀ Q
⋀-lambda Φ .*⊑* x p y = Φ .*⊑* ((x , y)) p

-- Existential quantification
⋁ : ∀ {X Y : Setoid o e} → Predicate (⊗-setoid X Y) → Predicate X
⋁ {X} {Y} P .Predicate.pred x = ∃ (Y .Setoid.Carrier) λ y → P .Predicate.pred (x , y)
⋁ {X} {Y} P .Predicate.pred-≃ x₁≈x₂ (y , p) = y , P .Predicate.pred-≃ (x₁≈x₂ , Y .Setoid.refl) p

⋁-in : ∀ {X Y : Setoid o e} {P : Predicate (⊗-setoid X Y)} →
        P ⊑ (⋁ P) [ project₁ ]
⋁-in .*⊑* (x , y) p = y , p

⋁-elim : ∀ {X Y : Setoid o e} {P : Predicate (⊗-setoid X Y)} {Q : Predicate X} →
          P ⊑ Q [ project₁ ] → ⋁ P ⊑ Q
⋁-elim Φ .*⊑* x (y , p) = Φ .*⊑* (x , y) p

⋁-frobenius : ∀ {X Y : Setoid o e} {P : Predicate (⊗-setoid X Y)} {Q : Predicate X} →
              ⋁ (P && (Q [ project₁ ])) ⊑ (⋁ P && Q)
⋁-frobenius {X} {Y} {P} {Q} .*⊑* x (y , p , q) = (y , p) , q

-- And the inverse...

-- Top
TT : ∀ {X} → Predicate X
TT .Predicate.pred x = ⊤
TT .Predicate.pred-≃ _ tt = tt

TT-isTop : ∀ {X} → IsTop ⊑-isPreorder (TT {X})
TT-isTop .IsTop.≤-top .*⊑* x _ = tt

[]-TT : ∀ {X Y} {f : X ⇒s Y} → TT ⊑ TT [ f ]
[]-TT .*⊑* _ tt = tt

-- Residuals / implication
_==>_ : ∀ {X : Setoid o e} → Predicate X → Predicate X → Predicate X
(P ==> Q) .Predicate.pred x = P .Predicate.pred x → Q .Predicate.pred x
_==>_ {X} P Q .Predicate.pred-≃ x₁≈x₂ ϕ p =
  Q .Predicate.pred-≃ x₁≈x₂ (ϕ (P .Predicate.pred-≃ (X .Setoid.sym x₁≈x₂) p))

==>-residual : ∀ {X} → IsResidual ⊑-isPreorder (monoidOfMeet _ &&-isMeet TT-isTop) (_==>_ {X})
==>-residual .IsResidual.lambda Φ .*⊑* x p q = Φ .*⊑* x (p , q)
==>-residual .IsResidual.eval .*⊑* x (f , p) = f p

[]-==> : ∀ {X Y : Setoid o e}{P Q : Predicate Y}{f : X ⇒s Y} → ((P [ f ]) ==> (Q [ f ])) ⊑ (P ==> Q) [ f ]
[]-==> .*⊑* x z = z


-- Joins / disjunction
_++_ : ∀ {X} → Predicate X → Predicate X → Predicate X
(P ++ Q) .Predicate.pred x = (P .Predicate.pred x) ∨ (Q .Predicate.pred x)
(P ++ Q) .Predicate.pred-≃ x₁≈x₂ (inj₁ p) = inj₁ (P .Predicate.pred-≃ x₁≈x₂ p)
(P ++ Q) .Predicate.pred-≃ x₁≈x₂ (inj₂ q) = inj₂ (Q .Predicate.pred-≃ x₁≈x₂ q)

++-isJoin : ∀ {X} → IsJoin ⊑-isPreorder (_++_ {X})
++-isJoin .IsJoin.inl .*⊑* _ = inj₁
++-isJoin .IsJoin.inr .*⊑* _ = inj₂
++-isJoin .IsJoin.[_,_] ϕ ψ .*⊑* x (inj₁ p) = ϕ .*⊑* x p
++-isJoin .IsJoin.[_,_] ϕ ψ .*⊑* x (inj₂ q) = ψ .*⊑* x q

[]-++ : ∀ {X Y} {P Q : Predicate Y} {f : X ⇒s Y} → ((P ++ Q) [ f ]) ⊑ ((P [ f ]) ++ (Q [ f ]))
[]-++ .*⊑* x p = p

-- Equality
Eq : ∀ X → Predicate (⊗-setoid X X)
Eq X .Predicate.pred (x , x') = LiftP o (X .Setoid._≈_ x x')
Eq X .Predicate.pred-≃ {x₁ , x'₁} {x₂ , x'₂} (x₁≈x₂ , x'₁≈x'₂) (lift eq) =
  lift (begin x₂ ≈˘⟨ x₁≈x₂ ⟩ x₁ ≈⟨ eq ⟩ x'₁ ≈⟨ x'₁≈x'₂ ⟩ x'₂ ∎)
  where open ≈-Reasoning (X .Setoid.isEquivalence)

dup : ∀ {X : Setoid o e} → X ⇒s ⊗-setoid X X
dup = pair (idS _) (idS _)

refl : ∀ {X} → TT ⊑ Eq X [ dup ]
refl {X} .*⊑* x tt .lower = X .Setoid.refl

-- subst : ∀ {X}

open import predicate-system

system : PredicateSystem (SetoidCat o e) (Setoid-products o e)
system .PredicateSystem.Predicate = Predicate
system .PredicateSystem._⊑_ = _⊑_
system .PredicateSystem._[_] = _[_]
system .PredicateSystem._⟨_⟩ = _⟨_⟩
system .PredicateSystem.adjoint₁ = adjoint₁
system .PredicateSystem.adjoint₂ = adjoint₂
system .PredicateSystem.TT = TT
system .PredicateSystem._&&_ = _&&_
system .PredicateSystem._++_ = _++_
system .PredicateSystem._==>_ = _==>_
system .PredicateSystem.⋀ = ⋀
system .PredicateSystem.⊑-isPreorder = ⊑-isPreorder
system .PredicateSystem._[_]m = _[_]m
system .PredicateSystem.[]-cong = []-cong
system .PredicateSystem.[]-id = []-id
system .PredicateSystem.[]-id⁻¹ = []-id⁻¹
system .PredicateSystem.[]-comp = []-comp
system .PredicateSystem.[]-comp⁻¹ = []-comp⁻¹
system .PredicateSystem.TT-isTop = TT-isTop
system .PredicateSystem.[]-TT = []-TT
system .PredicateSystem.&&-isMeet = &&-isMeet
system .PredicateSystem.[]-&& = []-&&
system .PredicateSystem.==>-residual = ==>-residual
system .PredicateSystem.[]-==> = []-==>
system .PredicateSystem.[]-++ = []-++
system .PredicateSystem.++-isJoin = ++-isJoin
system .PredicateSystem.⋀-[] = ⋀-[]
system .PredicateSystem.⋀-eval = ⋀-eval
system .PredicateSystem.⋀-lambda = ⋀-lambda
