{-# OPTIONS --prop --postfix-projections --safe #-}

module empty-diagram where

open import Level using (0ℓ)
open import prop-setoid using (IsEquivalence; module ≈-Reasoning)
open import categories using (Category; IsTerminal)
open import functor using (Functor; NatTrans; NatIso; IsLimit; ≃-NatTrans; constFmor)

open IsEquivalence

data Obj : Set where

-- No objects, no problems.
cat : Category 0ℓ 0ℓ 0ℓ
cat .Category.obj = Obj

module _ {o m e} (𝒞 : Category o m e) where

  private
    module 𝒞 = Category 𝒞

  initial-functor : Functor cat 𝒞
  initial-functor .Functor.fobj ()

  open Category.IsIso
  open NatTrans
  open NatIso
  open IsTerminal
  open IsLimit
  open ≃-NatTrans

  initial-functor-unique : ∀ {F G : Functor cat 𝒞} → NatIso F G
  initial-functor-unique .transform .transf ()
  initial-functor-unique .transf-iso ()

  limit→terminal : ∀ {F : Functor cat 𝒞} {t} {cone} →
                   IsLimit F t cone → IsTerminal 𝒞 t
  limit→terminal is-limit .to-terminal =
    is-limit .lambda _ (initial-functor-unique .transform)
  limit→terminal {F} {t} {cone} is-limit .to-terminal-ext {x} f = begin
      is-limit .lambda x (initial-functor-unique .transform)
    ≈⟨ is-limit .lambda-cong (record { transf-eq = λ () }) ⟩
      is-limit .lambda x (cone functor.∘ constFmor f)
    ≈⟨ is-limit .lambda-ext f ⟩
      f
    ∎
    where open ≈-Reasoning 𝒞.isEquiv

  terminal→limit : ∀ {t} →
                   IsTerminal 𝒞 t →
                   IsLimit initial-functor t (initial-functor-unique .transform)
  terminal→limit is-terminal .lambda x _ = is-terminal .to-terminal
  terminal→limit is-terminal .lambda-cong α≈β = 𝒞.≈-refl
  terminal→limit is-terminal .lambda-eval α .transf-eq ()
  terminal→limit is-terminal .lambda-ext = is-terminal .to-terminal-ext
