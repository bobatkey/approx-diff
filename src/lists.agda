{-# OPTIONS --postfix-projections --prop --safe #-}

{-

Construct list objects from infinite coproducts.

This is used to construct a list object in Fam⟨C⟩ categories, instead of doing it by hand.

TODO: prove that the recursion properties hold.

-}

open import Level using (0ℓ)
open import prop using (⟪_⟫; tt)
open import prop-setoid using (Setoid; IsEquivalence; module ≈-Reasoning)
open import categories using (Category; HasLists; setoid→category; HasTerminal; HasProducts; HasExponentials)
open import functor using (Functor; HasColimits; Colimit; IsColimit; NatTrans)
open import nat using (ℕ; ℕₛ; zero; succ; _≃_; succ-injective; succ-cong)

module lists
    {o m e}
    (𝒞 : Category o m e) (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞E : HasExponentials 𝒞 𝒞P)
       -- FIXME: really just need distributivity, not exponentials
    (hasDiscreteColimits : ∀ (A : Setoid 0ℓ 0ℓ) → HasColimits (setoid→category A) 𝒞)
  where

private
  module 𝒞 = Category 𝒞
  module 𝒞T = HasTerminal 𝒞T
  module 𝒞P = HasProducts 𝒞P
  module 𝒞E = HasExponentials 𝒞E
open Functor
open NatTrans

_^_ : 𝒞.obj → ℕ → 𝒞.obj
x ^ zero   = 𝒞T.witness
x ^ succ n = 𝒞P.prod (x ^ n) x

module _ (A : 𝒞.obj) where

  transport : ∀ {m n} → m ≃ n → (A ^ m) 𝒞.⇒ (A ^ n)
  transport {zero} {zero}     _  = 𝒞.id _
  transport {succ m} {succ n} eq = 𝒞P.prod-m (transport {m} {n} (succ-injective eq)) (𝒞.id _)

  ListF : Functor (setoid→category ℕₛ) 𝒞
  ListF .fobj n = A ^ n
  ListF .fmor ⟪ eq ⟫ = transport eq
  ListF .fmor-cong tt = 𝒞.≈-refl
  ListF .fmor-id {zero} = 𝒞.≈-refl
  ListF .fmor-id {succ m} = 𝒞.≈-trans (𝒞P.prod-m-cong (ListF .fmor-id {m}) 𝒞.≈-refl) 𝒞P.prod-m-id
  ListF .fmor-comp {zero}   {zero}   {zero}   x y = 𝒞.≈-sym 𝒞.id-left
  ListF .fmor-comp {succ m} {succ n} {succ o} ⟪ eq1 ⟫ ⟪ eq2 ⟫ = begin
      𝒞P.prod-m (transport {m} {o} _) (𝒞.id _)
    ≈⟨ 𝒞P.prod-m-cong (ListF .fmor-comp ⟪ succ-injective eq1 ⟫ ⟪ succ-injective eq2 ⟫) (𝒞.≈-sym 𝒞.id-left) ⟩
      𝒞P.prod-m (transport (succ-injective eq1) 𝒞.∘ transport (succ-injective eq2)) (𝒞.id _ 𝒞.∘ 𝒞.id _)
    ≈⟨ 𝒞P.pair-functorial _ _ _ _ ⟩
      𝒞P.prod-m (transport (succ-injective eq1)) (𝒞.id _) 𝒞.∘ 𝒞P.prod-m (transport (succ-injective eq2)) (𝒞.id _)
    ∎
    where open ≈-Reasoning 𝒞.isEquiv

  open Colimit (hasDiscreteColimits ℕₛ ListF)
  open IsColimit

  List : 𝒞.obj
  List = apex

  nil : 𝒞T.witness 𝒞.⇒ List
  nil = cocone .transf 0

  cons' : List 𝒞.⇒ 𝒞E.exp A List
  cons' = isColimit .colambda (𝒞E.exp A List) α
    where
      α : NatTrans ListF (functor.constF _ (𝒞E.exp A List))
      α .transf n = 𝒞E.lambda (cocone .transf (succ n))
      α .natural {m} {n} ⟪ eq ⟫ = begin
           𝒞.id _ 𝒞.∘ 𝒞E.lambda (cocone .transf (succ m))
         ≈⟨ 𝒞.id-left ⟩
           𝒞E.lambda (cocone .transf (succ m))
         ≈˘⟨ 𝒞E.lambda-cong 𝒞.id-left ⟩
           𝒞E.lambda (𝒞.id _ 𝒞.∘ cocone .transf (succ m))
         ≈⟨ 𝒞E.lambda-cong (cocone .natural {succ m} {succ n} ⟪ (succ-cong eq) ⟫) ⟩
           𝒞E.lambda (cocone .transf (succ n) 𝒞.∘ 𝒞P.prod-m (transport eq) (𝒞.id _))
         ≈˘⟨ 𝒞E.lambda-natural _ _ ⟩
           𝒞E.lambda (cocone .transf (succ n)) 𝒞.∘ transport eq
         ∎
         where open ≈-Reasoning 𝒞.isEquiv

  cons : 𝒞P.prod A List 𝒞.⇒ List
  cons = 𝒞E.eval 𝒞.∘ 𝒞P.pair (cons' 𝒞.∘ 𝒞P.p₂) 𝒞P.p₁

  fold' : ∀ {C} (nil-m : 𝒞T.witness 𝒞.⇒ C) (cons-m : 𝒞P.prod C A 𝒞.⇒ C) →
          List 𝒞.⇒ C
  fold' {C} nil-m cons-m = isColimit .colambda C α
    where
      α : NatTrans ListF (functor.constF _ C)
      α .transf zero     = nil-m
      α .transf (succ n) = cons-m 𝒞.∘ 𝒞P.prod-m (α .transf n) (𝒞.id _)
      α .natural {zero}   {zero}   ⟪ eq ⟫ = 𝒞.id-swap
      α .natural {succ m} {succ n} ⟪ eq ⟫ = begin
          𝒞.id C 𝒞.∘ (cons-m 𝒞.∘ 𝒞P.prod-m (α .transf m) (𝒞.id A))
        ≈⟨ 𝒞.id-left ⟩
          cons-m 𝒞.∘ 𝒞P.prod-m (α .transf m) (𝒞.id A)
        ≈˘⟨ 𝒞.∘-cong 𝒞.≈-refl (𝒞P.prod-m-cong 𝒞.id-left 𝒞.id-left) ⟩
          cons-m 𝒞.∘ 𝒞P.prod-m (𝒞.id _ 𝒞.∘ α .transf m) (𝒞.id _ 𝒞.∘ 𝒞.id _)
        ≈⟨ 𝒞.∘-cong 𝒞.≈-refl (𝒞P.prod-m-cong (α .natural {m} {n} ⟪ succ-injective eq ⟫) 𝒞.≈-refl) ⟩
          cons-m 𝒞.∘ 𝒞P.prod-m (α .transf n 𝒞.∘ transport (succ-injective eq)) (𝒞.id _ 𝒞.∘ 𝒞.id _)
        ≈⟨ 𝒞.∘-cong 𝒞.≈-refl (𝒞P.pair-functorial _ _ _ _) ⟩
          cons-m 𝒞.∘ (𝒞P.prod-m (α .transf n) (𝒞.id A) 𝒞.∘ 𝒞P.prod-m (transport {m} {n} _) (𝒞.id A))
        ≈˘⟨ 𝒞.assoc _ _ _ ⟩
         (cons-m 𝒞.∘ 𝒞P.prod-m (α .transf n) (𝒞.id A)) 𝒞.∘ 𝒞P.prod-m (transport (succ-injective eq)) (𝒞.id A)
        ∎
        where open ≈-Reasoning 𝒞.isEquiv


lists : HasLists 𝒞 𝒞T 𝒞P
lists .HasLists.list = List
lists .HasLists.nil {A} = nil A
lists .HasLists.cons {A} = cons A
lists .HasLists.fold {X} {A} {Y} nil-m cons-m =
  𝒞E.eval 𝒞.∘ 𝒞P.pair (fold' A nil-m' cons-m' 𝒞.∘ 𝒞P.p₂) 𝒞P.p₁
  where
    nil-m' : 𝒞T.witness 𝒞.⇒ 𝒞E.exp X Y
    nil-m' = 𝒞E.lambda (nil-m 𝒞.∘ 𝒞P.p₂)

    cons-m' : 𝒞P.prod (𝒞E.exp X Y) A 𝒞.⇒ 𝒞E.exp X Y
    cons-m' = 𝒞E.lambda (cons-m 𝒞.∘ 𝒞P.pair (𝒞P.pair 𝒞P.p₂ (𝒞P.p₂ 𝒞.∘ 𝒞P.p₁)) (𝒞E.eval 𝒞.∘ 𝒞P.pair (𝒞P.p₁ 𝒞.∘ 𝒞P.p₁) 𝒞P.p₂))
