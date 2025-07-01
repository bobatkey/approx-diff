{-# OPTIONS --postfix-projections --prop #-}

module conservativity where

open import Level using (Lift; lift; lower; _⊔_)
open import Data.Product using (_,_)
open import prop using (_,_; proj₁; proj₂; ∃; LiftP; lift; lower; liftS; LiftS; inj₁; inj₂)
open import basics using (module ≤-Reasoning; IsClosureOp; IsJoin)
open import categories using (Category; HasBooleans; HasProducts; HasCoproducts; HasExponentials; HasTerminal; IsTerminal; IsProduct; coproducts+exp→booleans)
open import functor using (Functor; _∘F_; opF; _∘H_; ∘H-cong; id; _∘_; NatTrans; ≃-NatTrans; ≃-isEquivalence; interchange; NT-id-left)
open import prop-setoid using (module ≈-Reasoning; IsEquivalence)
open import setoid-cat using (SetoidCat)
open import predicate-system using (PredicateSystem)
import sconing
import glueing-simple
import setoid-predicate

import language-syntax
import language-interpretation
open import signature

open Functor

-- Let Sig be a signature
-- Let M be a model of Sig in 𝒞, and F be a finite product and infinite coproduct preserving functor
-- Then:
--   1. Can interpret the whole language in Glued
--   2. Every first order type is isomorphic to its interpretation in 𝒞
--   3. So every judgement x : A ⊢ M : B, with A, B first-order, has a morphism g : A 𝒞.⇒ B such that F(g) = ⟦ M ⟧

-- For the actual language:
--  1. 𝒞 = Fam⟨LatGal⟩ which has finite products and infinite coproducts
--  2. 𝒟 = Fam⟨M×J^op⟩ which is a BiCCC
--  3. F  = Fam⟨𝓖⟩ which preserves products and infinite coproducts
-- Could also replay the whole thing with `Stable` instead of Fam⟨LatGal⟩ ??

-- TODO:
--   1. Chosen (co)product preserving functors
--   2. Finish holes in presheaf-predicate
--   3. id ∘H id = id
--   4. Finish lemma2 (prove equalities)
--   5. GF .fmor f .presv
--   6. G preserves (chosen) products
--   7. Stability: prove it for Fam⟨𝒞⟩ (!!!)
--   8. GF preserves products and terminal object (should be true for any predicate system)
--   9. Finish 'tidy', which is properly the fact that GP is closed


module _ {ℓ} (Sig : Signature ℓ)
         {o m e}
         -- Category for interpreting first-order things
         (𝒞 : Category o m e) (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞CP : HasCoproducts 𝒞)
         (Int : Model PFPC[ 𝒞 , 𝒞T , 𝒞P , {!!} ] Sig)
         -- A higher order model
         (𝒟 : Category o m e)
         (𝒟T : HasTerminal 𝒟) (𝒟P : HasProducts 𝒟) (𝒟CP : HasCoproducts 𝒟) (𝒟E : HasExponentials 𝒟 𝒟P)
         -- A functor which preserves finite products (and the boolean object)
         (F  : Functor 𝒞 𝒟) (FP : FPFunctor F)
         (F-coprod : ∀ {x y} → 𝒟 .Category._⇒_ (F .fobj (𝒞CP .HasCoproducts.coprod x y))
                                                (𝒟CP .HasCoproducts.coprod (F .fobj x) (F .fobj y)))
  where

  private
    module 𝒞 = Category 𝒞
    module 𝒞P = HasProducts 𝒞P
    module 𝒞CP = HasCoproducts 𝒞CP
    module 𝒟 = Category 𝒟
    module 𝒟P = HasProducts 𝒟P
    module 𝒟CP = HasCoproducts 𝒟CP

{-
  module L = language-syntax.language Sig

  module 𝒟Interp =
    language-interpretation
      Sig
      𝒟 𝒟T 𝒟P 𝒟E (coproducts+exp→booleans 𝒟T 𝒟CP 𝒟E)
      (transport-model Sig F FP {!!} Int)
-}

  open import yoneda (m ⊔ e) 𝒞 renaming (PSh to PSh⟨𝒞⟩; products to PSh⟨𝒞⟩-products; exponentials to PSh⟨𝒞⟩-exponentials)
  open import yoneda (m ⊔ e) 𝒟 renaming (よ to 𝒟よ) using ()

  private
    module PSh⟨𝒞⟩ = Category PSh⟨𝒞⟩
    module PSh⟨𝒞⟩P = HasProducts PSh⟨𝒞⟩-products
  open NatTrans
  open ≃-NatTrans

  G : Functor 𝒟 PSh⟨𝒞⟩
  G .fobj x = 𝒟よ .fobj x ∘F opF F
  G .fmor f = 𝒟よ .fmor f ∘H id _
  G .fmor-cong f₁≈f₂ = ∘H-cong (𝒟よ .fmor-cong f₁≈f₂) (≃-isEquivalence .IsEquivalence.refl)
  G .fmor-id = begin
      𝒟よ .fmor (𝒟.id _) ∘H id _
    ≈⟨ ∘H-cong (𝒟よ .fmor-id) (≃-isEquivalence .IsEquivalence.refl) ⟩
      id _ ∘H id _
    ≈⟨ record { transf-eq = λ x₁ → record { func-eq = λ e → lift (𝒟.≈-trans 𝒟.id-right (e .lower)) } } ⟩ -- FIXME: put this in functor.agda
      PSh⟨𝒞⟩.id _
    ∎ where open ≈-Reasoning PSh⟨𝒞⟩.isEquiv
  G .fmor-comp f g = begin
      𝒟よ .fmor (f 𝒟.∘ g) ∘H id _
    ≈⟨ ∘H-cong (𝒟よ .fmor-comp f g) (≃-isEquivalence .IsEquivalence.sym NT-id-left) ⟩
      (𝒟よ .fmor f ∘ 𝒟よ .fmor g) ∘H (id _ ∘ id _)
    ≈⟨ interchange _ _ _ _ ⟩
      (𝒟よ .fmor f ∘H id _) PSh⟨𝒞⟩.∘ (𝒟よ .fmor g ∘H id _)
    ∎ where open ≈-Reasoning PSh⟨𝒞⟩.isEquiv

  module _ where
    open prop-setoid._⇒_
    open prop-setoid._≃m_

    G-prod : ∀ {x y} → PSh⟨𝒞⟩P.prod (G .fobj x) (G .fobj y) PSh⟨𝒞⟩.⇒ G .fobj (𝒟P.prod x y)
    G-prod {X} {Y} .transf x .func (lift f , lift g) = lift (𝒟P.pair f g)
    G-prod {X} {Y} .transf x .func-resp-≈ (lift f₁≈f₂ , lift g₁≈g₂) = lift (𝒟P.pair-cong f₁≈f₂ g₁≈g₂)
    G-prod {X} {Y} .natural f .func-eq {lift x₁ , lift y₁} {lift x₂ , lift y₂} (lift x₁≈x₂ , lift y₁≈y₂) =
      lift (begin
        𝒟P.pair x₁ y₁ 𝒟.∘ F .fmor f
      ≈⟨ 𝒟.∘-cong (𝒟P.pair-cong x₁≈x₂ y₁≈y₂) 𝒟.≈-refl ⟩
        𝒟P.pair x₂ y₂ 𝒟.∘ F .fmor f
      ≈⟨ 𝒟P.pair-natural _ _ _ ⟩
        𝒟P.pair (x₂ 𝒟.∘ F .fmor f) (y₂ 𝒟.∘ F .fmor f)
      ∎)
      where open ≈-Reasoning 𝒟.isEquiv

    G-prod⁻¹ : ∀ {x y} → G .fobj (𝒟P.prod x y) PSh⟨𝒞⟩.⇒ PSh⟨𝒞⟩P.prod (G .fobj x) (G .fobj y)
    G-prod⁻¹ = PSh⟨𝒞⟩P.pair (G .fmor 𝒟P.p₁) (G .fmor 𝒟P.p₂)

  open import presheaf-predicate (m ⊔ e) 𝒞
    renaming (system to PSh⟨𝒞⟩-system; Predicate to PShPredicate)
    using (_⊑_; module CoproductMonad; _++_; _⟨_⟩; StableBits; ⊑-isPreorder; _[_]; []-++; ++-isJoin)

  module PSh⟨𝒞⟩-system = PredicateSystem PSh⟨𝒞⟩-system

  open PShPredicate
  open setoid-predicate.Predicate
  open setoid-predicate._⊑_

  GP : ∀ x → PShPredicate (G .fobj (F .fobj x))
  GP x .pred y .pred (lift f) = LiftP o (∃ (y 𝒞.⇒ x) λ g → F .fmor g 𝒟.≈ f)
  GP x .pred y .pred-≃ {lift f₁} {lift f₂} (lift f₁≈f₂) (lift (g , eq)) = lift (g , 𝒟.≈-trans eq f₁≈f₂)
  GP x .pred-mor h .*⊑* (lift f) (lift (g , eq)) =
     lift (g 𝒞.∘ h , 𝒟.≈-trans (F .fmor-comp g h) (𝒟.∘-cong eq 𝒟.≈-refl))

  postulate
    -- FIXME: put this in the parameters for the module
    stability : ∀ {x₁ x₂ x y} f g → StableBits 𝒞CP {x₁} {x₂} {x} {y} f g
  open CoproductMonad 𝒞CP stability

  open _⊑_

  lemma2 : ∀ {x y} →
           GP (𝒞CP.coprod x y) ⊑
           𝐂 ((GP x ⟨ G .fmor (F .fmor 𝒞CP.in₁) ⟩) ++ (GP y ⟨ G .fmor (F .fmor 𝒞CP.in₂) ⟩))
  lemma2 .*⊑* z .*⊑* (lift g) (lift (f , eq)) =
    liftS (node (stb .StableBits.y₁) (stb .StableBits.y₂)
                (lift (F .fmor (𝒞CP.in₁ 𝒞.∘ stb .StableBits.h₁)))
                (lift (F .fmor (𝒞CP.in₂ 𝒞.∘ stb .StableBits.h₂)))
                (stb .StableBits.h)
                (leaf (inj₁ (lift (F .fmor (stb .StableBits.h₁)) , lift (stb .StableBits.h₁ , 𝒟.≈-refl) , lift {!!})))
                (leaf (inj₂ (lift (F .fmor (stb .StableBits.h₂)) , lift (stb .StableBits.h₂ , 𝒟.≈-refl) , lift {!!})))
                (lift {!!})
                (lift {!!}))
    where stb = stability 𝒞.Iso-refl f

  open import closure-predicate PSh⟨𝒞⟩ PSh⟨𝒞⟩-products PSh⟨𝒞⟩-system closureOp
    using (system; Predicate; embed)

  module Gl = glueing-simple 𝒟 PSh⟨𝒞⟩ _ system G
  module GlCP = Gl.coproducts 𝒟CP
  module GlCPM = HasCoproducts (GlCP.coproducts)
  module GlPE = Gl.products-and-exponentials 𝒟T 𝒟P 𝒟E G-prod G-prod⁻¹ {!!} {!!} {!!}
  module GlPM = HasProducts GlPE.products

  module Glued = Category Gl.cat
  open Gl.Obj
  open Gl._=>_
  open Gl._≃m_
  open Predicate

  GF : Functor 𝒞 Gl.cat
  GF .fobj x .carrier = F .fobj x
  GF .fobj x .pred = embed (GP x)
  GF .fmor f .morph = F .fmor f
  GF .fmor {x} {y} f .presv = begin
      𝐂 (GP x)
    ≤⟨ 𝐂-isClosure .IsClosureOp.mono (record { *⊑* = λ a → record { *⊑* = λ g e → lift {!!} } }) ⟩
      𝐂 (GP y [ G .fmor (F .fmor f) ])
    ≤⟨ 𝐂-[] ⟩
      𝐂 (GP y) [ G .fmor (F .fmor f) ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder
  GF .fmor-cong f₁≈f₂ .f≃f = F .fmor-cong f₁≈f₂
  GF .fmor-id .f≃f = F .fmor-id
  GF .fmor-comp f g .f≃f = F .fmor-comp f g

  -- GF should be a finite product and coproduct preserving functor

  presv-prod : ∀ {x y} → GlPM.prod (GF .fobj x) (GF .fobj y) Glued.⇒ GF .fobj (𝒞P.prod x y)
  presv-prod {x} {y} .morph = {!F-prod!}
  presv-prod {x} {y} .presv = {!!}

  presv-cp : ∀ {x y} → GF .fobj (𝒞CP.coprod x y) Glued.⇒ GlCPM.coprod (GF .fobj x) (GF .fobj y)
  presv-cp {x} {y} .morph = F-coprod
  presv-cp {x} {y} .presv = begin
      𝐂 (GP (𝒞CP.coprod x y))
    ≤⟨ 𝐂-isClosure .IsClosureOp.mono lemma2 ⟩
      𝐂 (𝐂 ((GP x ⟨ G .fmor (F .fmor 𝒞CP.in₁) ⟩) ++ (GP y ⟨ G .fmor (F .fmor 𝒞CP.in₂) ⟩)))
    ≤⟨ 𝐂-isClosure .IsClosureOp.closed ⟩
      𝐂 ((GP x ⟨ G .fmor (F .fmor 𝒞CP.in₁) ⟩) ++ (GP y ⟨ G .fmor (F .fmor 𝒞CP.in₂) ⟩))
    ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsJoin.mono ++-isJoin ((𝐂-isClosure .IsClosureOp.unit) PSh⟨𝒞⟩-system.⟨ _ ⟩m) ((𝐂-isClosure .IsClosureOp.unit) PSh⟨𝒞⟩-system.⟨ _ ⟩m)) ⟩
      𝐂 ((𝐂 (GP x) ⟨ G .fmor (F .fmor 𝒞CP.in₁) ⟩) ++ (𝐂 (GP y) ⟨ G .fmor (F .fmor 𝒞CP.in₂) ⟩))
    ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsJoin.mono ++-isJoin (𝐂-isClosure .IsClosureOp.unit) (𝐂-isClosure .IsClosureOp.unit)) ⟩
      𝐂 ((𝐂 (𝐂 (GP x) ⟨ G .fmor (F .fmor 𝒞CP.in₁) ⟩)) ++ (𝐂 (𝐂 (GP y) ⟨ G .fmor (F .fmor 𝒞CP.in₂) ⟩)))
    ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsJoin.mono ++-isJoin (𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.unit _)) (𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.unit _))) ⟩
      𝐂 ((𝐂 (𝐂 (GP x) ⟨ G .fmor (F .fmor 𝒞CP.in₁) ⟩ ⟨ G .fmor F-coprod ⟩ [ G .fmor F-coprod ])) ++ (𝐂 (𝐂 (GP y) ⟨ G .fmor (F .fmor 𝒞CP.in₂) ⟩ ⟨ G .fmor F-coprod ⟩ [ G .fmor F-coprod ])))
    ≤⟨ 𝐂-isClosure .IsClosureOp.mono
          (IsJoin.mono ++-isJoin (𝐂-isClosure .IsClosureOp.mono ({!PSh⟨𝒞⟩-system.⟨⟩-comp _ _!} PSh⟨𝒞⟩-system.[ _ ]m))
                                 (𝐂-isClosure .IsClosureOp.mono ({!PSh⟨𝒞⟩-system.⟨⟩-comp _ _!} PSh⟨𝒞⟩-system.[ _ ]m))) ⟩
      𝐂 ((𝐂 (𝐂 (GP x) ⟨ G .fmor F-coprod PSh⟨𝒞⟩.∘ G .fmor (F .fmor 𝒞CP.in₁) ⟩ [ G .fmor F-coprod ])) ++ (𝐂 (𝐂 (GP y) ⟨ G .fmor F-coprod PSh⟨𝒞⟩.∘ G .fmor (F .fmor 𝒞CP.in₂) ⟩ [ G .fmor F-coprod ])))
    ≤⟨ 𝐂-isClosure .IsClosureOp.mono
          (IsJoin.mono ++-isJoin (𝐂-isClosure .IsClosureOp.mono ({!PSh⟨𝒞⟩-system.⟨⟩-cong!} PSh⟨𝒞⟩-system.[ _ ]m))
                                 (𝐂-isClosure .IsClosureOp.mono ({!PSh⟨𝒞⟩-system.⟨⟩-cong!} PSh⟨𝒞⟩-system.[ _ ]m))) ⟩
      𝐂 ((𝐂 (𝐂 (GP x) ⟨ G .fmor (F-coprod 𝒟.∘ F .fmor 𝒞CP.in₁) ⟩ [ G .fmor F-coprod ])) ++ (𝐂 (𝐂 (GP y) ⟨ G .fmor (F-coprod 𝒟.∘ F .fmor 𝒞CP.in₂) ⟩ [ G .fmor F-coprod ])))
    ≤⟨ 𝐂-isClosure .IsClosureOp.mono
          (IsJoin.mono ++-isJoin (𝐂-isClosure .IsClosureOp.mono ({!PSh⟨𝒞⟩-system.⟨⟩-cong!} PSh⟨𝒞⟩-system.[ _ ]m))
                                 (𝐂-isClosure .IsClosureOp.mono ({!PSh⟨𝒞⟩-system.⟨⟩-cong!} PSh⟨𝒞⟩-system.[ _ ]m))) ⟩
      𝐂 ((𝐂 (𝐂 (GP x) ⟨ G .fmor 𝒟CP.in₁ ⟩ [ G .fmor F-coprod ])) ++ (𝐂 (𝐂 (GP y) ⟨ G .fmor 𝒟CP.in₂ ⟩ [ G .fmor F-coprod ])))
    ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsJoin.mono ++-isJoin 𝐂-[] 𝐂-[]) ⟩
      𝐂 ((𝐂 (𝐂 (GP x) ⟨ G .fmor 𝒟CP.in₁ ⟩) [ G .fmor F-coprod ]) ++ (𝐂 (𝐂 (GP y) ⟨ G .fmor 𝒟CP.in₂ ⟩) [ G .fmor F-coprod ]))
    ≤⟨ 𝐂-isClosure .IsClosureOp.mono {![]-++⁻¹!} ⟩
      𝐂 ((𝐂 (𝐂 (GP x) ⟨ G .fmor 𝒟CP.in₁ ⟩) ++ 𝐂 (𝐂 (GP y) ⟨ G .fmor 𝒟CP.in₂ ⟩)) [ G .fmor F-coprod ])
    ≤⟨ 𝐂-[] ⟩
      𝐂 (𝐂 (𝐂 (GP x) ⟨ G .fmor 𝒟CP.in₁ ⟩) ++ 𝐂 (𝐂 (GP y) ⟨ G .fmor 𝒟CP.in₂ ⟩)) [ G .fmor F-coprod ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder

-- F-coprod 𝒟.∘ F .fobj 𝒞CP.in₁ = 𝒟CP.in₁

  open 𝒞.Iso

  GP-closed : ∀ {X Y} (f : F .fobj X 𝒟.⇒ F .fobj Y) →
         Context (G .fobj (F .fobj Y)) (GP Y) X (lift f) →
         ∃ (X 𝒞.⇒ Y) (λ g → F .fmor g 𝒟.≈ f)
  GP-closed f (leaf (lift p)) = p
  GP-closed f (node X₁ X₂ (lift f₁) (lift f₂) g t₁ t₂ (lift eq₁) (lift eq₂)) with GP-closed f₁ t₁
  ... | (g₁ , eq₃) with GP-closed f₂ t₂
  ... | (g₂ , eq₄) = 𝒞CP.copair g₁ g₂ 𝒞.∘ g .bwd ,
        (begin
          F .fmor (𝒞CP.copair g₁ g₂ 𝒞.∘ g .bwd)
        ≈⟨ {!!} ⟩ -- FIXME: use the fact that F-coprod ought to be an isomorphism
          (f 𝒟.∘ F .fmor (g .fwd)) 𝒟.∘ F .fmor (g .bwd)
        ≈⟨ 𝒟.assoc _ _ _ ⟩
          f 𝒟.∘ (F .fmor (g .fwd) 𝒟.∘ F .fmor (g .bwd))
        ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-comp _ _) ⟩
          f 𝒟.∘ F .fmor (g .fwd 𝒞.∘ g .bwd)
        ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-cong (g .fwd∘bwd≈id)) ⟩
          f 𝒟.∘ F .fmor (𝒞.id _)
        ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-id) ⟩
          f 𝒟.∘ 𝒟.id _
        ≈⟨ 𝒟.id-right ⟩
          f
        ∎)
    where open ≈-Reasoning 𝒟.isEquiv

      -- F .fmor g₁ ≈ f ∘ F .fmor (g .fwd ∘ in₁)
      -- F .fmor g₂ ≈ f ∘ F .fmor (g .fwd ∘ in₂)

  thm : ∀ {X Y} → (f : GF .fobj X Glued.⇒ GF .fobj Y) → ∃ (X 𝒞.⇒ Y) (λ g → F .fmor g 𝒟.≈ f .morph)
  thm {X} {Y} f with f .presv .*⊑* X .*⊑* (lift (F .fmor (𝒞.id _))) (liftS (leaf (lift (𝒞.id _ , 𝒟.≈-refl))))
  ... | (liftS t) with GP-closed _ t
  ... | g , eq = g , (begin
          F .fmor g
        ≈⟨ eq ⟩
          f .morph 𝒟.∘ (F .fmor (𝒞.id _) 𝒟.∘ 𝒟.id _)
        ≈⟨ 𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right ⟩
          f .morph 𝒟.∘ F .fmor (𝒞.id _)
        ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-id) ⟩
          f .morph 𝒟.∘ 𝒟.id _
        ≈⟨ 𝒟.id-right ⟩
          f .morph
        ∎)
        where open ≈-Reasoning 𝒟.isEquiv


  -- Now need to prove that for first-order types and contexts, the interpretation is preserved.

{-
  module glued (Env : Category.obj 𝒞) where

    module Sc = sconing 𝒟 𝒟P (F .fobj Env)
    open Sc using (Scone)

    module G = glueing-simple 𝒟 (SetoidCat m e) _ _ setoid-predicate.system Sc.Scone
    module GCP = G.coproducts 𝒟CP
    module GPE = G.products-and-exponentials 𝒟T 𝒟P 𝒟E Sc.mul Sc.mul⁻¹ Sc.mul-inv Sc.mul-natural Sc.Scone-p₁

    module Glued = Category G.cat
    open G.Obj
    open G._=>_
    open G._≃m_
    open setoid-predicate.Predicate
    open setoid-predicate._⊑_

    GF : Functor 𝒞 G.cat
    GF .fobj x .carrier = F .fobj x
    GF .fobj x .pred .pred f = ∃ (Env 𝒞.⇒ x) λ g → F .fmor g 𝒟.≈ f
    GF .fobj x .pred .pred-≃ f₁≈f₂ (g , eq) = g , 𝒟.≈-trans eq f₁≈f₂
    GF .fmor f .morph = F .fmor f
    GF .fmor f .presv .*⊑* f' (g , eq) =
      (f 𝒞.∘ g) , (begin
        F .fmor (f 𝒞.∘ g)        ≈⟨ F .fmor-comp f g ⟩
        F .fmor f 𝒟.∘ F .fmor g  ≈⟨ 𝒟.∘-cong 𝒟.≈-refl eq ⟩
        F .fmor f 𝒟.∘ f'         ∎)
      where open ≈-Reasoning 𝒟.isEquiv
    GF .fmor-cong f₁≈f₂ .f≃f = F .fmor-cong f₁≈f₂
    GF .fmor-id .f≃f = F .fmor-id
    GF .fmor-comp f g .f≃f = F .fmor-comp f g

    module _ where
      open FPFunctor
      open IsTerminal
      open IsProduct

      -- If F preserves finite products, then so does GF.
      GF-FP : FPFunctor GF
      GF-FP .preserve-terminal t t-isTerminal .to-terminal .morph =
        FP .preserve-terminal t t-isTerminal .to-terminal
      GF-FP .preserve-terminal t t-isTerminal .to-terminal {X} .presv .*⊑* g g∈X =
        t-isTerminal .to-terminal ,
        IsTerminal.to-terminal-unique (FP .preserve-terminal t t-isTerminal) _ _
      GF-FP .preserve-terminal t t-isTerminal .to-terminal-ext f .f≃f =
        FP .preserve-terminal t t-isTerminal .to-terminal-ext _

      GF-FP .preserve-products x y xy p₁ p₂ is-product .pair f g .morph =
        FP .preserve-products x y xy p₁ p₂ is-product .pair (f .morph) (g .morph)
      GF-FP .preserve-products x y xy p₁ p₂ is-product .pair {Z} f g .presv .*⊑* h h∈Z with f .presv .*⊑* h h∈Z
      ... | h₁ , eq₁ with g .presv .*⊑* h h∈Z
      ... | h₂ , eq₂ =
        is-product .pair h₁ h₂ ,
        (begin
          F .fmor (pair is-product h₁ h₂)
        ≈˘⟨ PP.pair-ext _ ⟩
          PP.pair (F .fmor p₁ 𝒟.∘ F .fmor (pair is-product h₁ h₂)) (F .fmor p₂ 𝒟.∘ F .fmor (pair is-product h₁ h₂))
        ≈˘⟨ PP.pair-cong (F .fmor-comp _ _) (F .fmor-comp _ _) ⟩
          PP.pair (F .fmor (p₁ 𝒞.∘ pair is-product h₁ h₂)) (F .fmor (p₂ 𝒞.∘ pair is-product h₁ h₂))
        ≈⟨ PP.pair-cong (F .fmor-cong (is-product .pair-p₁ _ _)) (F .fmor-cong (is-product .pair-p₂ _ _)) ⟩
          PP.pair (F .fmor h₁) (F .fmor h₂)
        ≈⟨ PP.pair-cong eq₁ eq₂ ⟩
          PP.pair (f .morph 𝒟.∘ h) (g .morph 𝒟.∘ h)
        ≈˘⟨ PP.pair-natural _ _ _ ⟩
          PP.pair (f .morph) (g .morph) 𝒟.∘ h
        ∎)
        where open ≈-Reasoning 𝒟.isEquiv
              module PP = IsProduct (FP .preserve-products x y xy p₁ p₂ is-product)
      GF-FP .preserve-products x y xy p₁ p₂ is-product .pair-cong f₁≈f₂ g₁≈g₂ .f≃f =
        FP .preserve-products _ _ _ _ _ is-product .pair-cong (f₁≈f₂ .f≃f) (g₁≈g₂ .f≃f)
      GF-FP .preserve-products x y xy p₁ p₂ is-product .pair-p₁ f g .f≃f =
        FP .preserve-products _ _ _ _ _ is-product .pair-p₁ _ _
      GF-FP .preserve-products x y xy p₁ p₂ is-product .pair-p₂ f g .f≃f =
        FP .preserve-products _ _ _ _ _ is-product .pair-p₂ _ _
      GF-FP .preserve-products x y xy p₁ p₂ is-product .pair-ext f .f≃f =
        FP .preserve-products _ _ _ _ _ is-product .pair-ext _

    thm : ∀ Y → (f : GF .fobj Env Glued.⇒ GF .fobj Y) → ∃ (Env 𝒞.⇒ Y) (λ g → F .fmor g 𝒟.≈ f .morph)
    thm Y f with f .presv .*⊑* (F .fmor (𝒞.id _)) (𝒞.id _ , 𝒟.≈-refl)
    ... | g , eq = g , (begin
                          F .fmor g                          ≈⟨ eq ⟩
                          f .morph 𝒟.∘ F .fmor (𝒞.id _)     ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-id) ⟩
                          f .morph 𝒟.∘ 𝒟.id _               ≈⟨ 𝒟.id-right ⟩
                          f .morph                           ∎)
      where open ≈-Reasoning 𝒟.isEquiv

    module LI = language-interpretation
                  Sig G.cat GPE.terminal GPE.products GPE.exponentials
                  (coproducts+exp→booleans GPE.terminal GCP.coproducts GPE.exponentials)
                  (transport-model Sig GF GF-FP {!!} Int)

    open L hiding (pair)

    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    open 𝒟.Iso
    open HasProducts 𝒟P
    open HasExponentials 𝒟E

    type-interp-iso : (τ : type) → 𝒟.Iso (LI.⟦ τ ⟧ty .carrier) 𝒟Interp.⟦ τ ⟧ty
    type-interp-iso unit = 𝒟.Iso-refl
    type-interp-iso bool = 𝒟.Iso-refl
    type-interp-iso (base s) = 𝒟.Iso-refl
    type-interp-iso (σ [×] τ) = product-preserves-iso (type-interp-iso σ) (type-interp-iso τ)
    type-interp-iso (σ [→] τ) = exp-preserves-iso (type-interp-iso σ) (type-interp-iso τ)

    ctxt-interp-iso : (Γ : ctxt) → 𝒟.Iso (LI.⟦ Γ ⟧ctxt .carrier) 𝒟Interp.⟦ Γ ⟧ctxt
    ctxt-interp-iso L.emp = 𝒟.Iso-refl
    ctxt-interp-iso (Γ L., τ) = product-preserves-iso (ctxt-interp-iso Γ) (type-interp-iso τ)

    project-all : ∀ {Γ τ} (M : Γ ⊢ τ) →
                  LI.⟦ M ⟧tm .morph 𝒟.≈ {!!} -- 𝒟Interp.⟦ M ⟧tm
    project-all = {!!}

  open L

  ⟦_⟧fo : ∀ {τ} → L.first-order τ → 𝒞.obj
  ⟦ unit ⟧fo = 𝒞T .HasTerminal.witness
  ⟦ bool ⟧fo = {!!}
  ⟦ base s ⟧fo = Int .Model.⟦sort⟧ s
  ⟦ τ₁ [×] τ₂ ⟧fo = 𝒞P .HasProducts.prod ⟦ τ₁ ⟧fo ⟦ τ₂ ⟧fo

  ⟦_⟧fo-ctxt : ∀ {Γ} → first-order-ctxt Γ → 𝒞.obj
  ⟦ emp ⟧fo-ctxt = 𝒞T .HasTerminal.witness
  ⟦ Γ L., τ ⟧fo-ctxt = 𝒞P .HasProducts.prod ⟦ Γ ⟧fo-ctxt ⟦ τ ⟧fo

  -- The interpretation of first-order types is isomorphic
  --    FIXME: this ought to be done in the glued category?
  fo-iso : ∀ {τ} (τ-fo : first-order τ) → 𝒟.Iso (F .fobj ⟦ τ-fo ⟧fo) (𝒟Interp.⟦ τ ⟧ty)
  fo-iso = {!!}

  fo-ctxt-iso : ∀ {Γ} (Γ-fo : first-order-ctxt Γ) → 𝒟.Iso (F .fobj ⟦ Γ-fo ⟧fo-ctxt) (𝒟Interp.⟦ Γ ⟧ctxt)
  fo-ctxt-iso = {!!}

  thm2 : ∀ {Γ τ} →
         (Γ-fo : first-order-ctxt Γ) →
         (τ-fo : first-order τ) →
         (M : Γ ⊢ τ) →
         ∃ (⟦ Γ-fo ⟧fo-ctxt 𝒞.⇒ ⟦ τ-fo ⟧fo)
           λ g → F .fmor g 𝒟.≈
                 (𝒟.Iso.bwd (fo-iso τ-fo) 𝒟.∘ (𝒟Interp.⟦ M ⟧tm 𝒟.∘ 𝒟.Iso.fwd (fo-ctxt-iso Γ-fo)))
  thm2 {Γ} {τ} Γ-fo τ-fo M = {!thm ⟦ τ-fo ⟧fo ⟦M⟧' !}
    where open glued ⟦ Γ-fo ⟧fo-ctxt
          ⟦M⟧ : LI.⟦ Γ ⟧ctxt Glued.⇒ LI.⟦ τ ⟧ty
          ⟦M⟧ = LI.⟦ M ⟧tm

          ⟦M⟧' : GF .fobj ⟦ Γ-fo ⟧fo-ctxt Glued.⇒ GF .fobj ⟦ τ-fo ⟧fo
          ⟦M⟧' = {!!} Glued.∘ (⟦M⟧ Glued.∘ {!!})

          eq : ⟦M⟧' .G._=>_.morph 𝒟.≈ (𝒟.Iso.bwd (fo-iso τ-fo) 𝒟.∘ (𝒟Interp.⟦ M ⟧tm 𝒟.∘ 𝒟.Iso.fwd (fo-ctxt-iso Γ-fo)))
          eq = {!!}
-}
