{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level
open import prop
open import categories
open import functor
open import commutative-monoid
open import cmon-enriched
open import commutative-monoid-cat using (_⇒_) renaming (cat to CMon; Obj to CMonObj)

module cmon-yoneda {o m e} os es (𝒞 : Category o m e) (CM𝒞 : CMonEnriched 𝒞) where

import yoneda os es 𝒞 as yoneda

PSh = [ opposite 𝒞 ⇒ CMon (m ⊔ os) (e ⊔ es) ]

private
  module 𝒞 = Category 𝒞
open _⇒_
open _=[_]>_
open CommutativeMonoid
open CMonObj
open Functor
open NatTrans
open ≃-NatTrans

open CMonEnriched CM𝒞

よ₀ : 𝒞.obj → PSh .Category.obj
よ₀ x .fobj y .carrier = yoneda.よ₀ x .fobj y
よ₀ x .fobj y .commMonoid .ε = lift εm
よ₀ x .fobj y .commMonoid ._+_ (lift f) (lift g) = lift (f +m g)
よ₀ x .fobj y .commMonoid .+-cong (lift e₁) (lift e₂) = lift (homCM _ _ .+-cong e₁ e₂)
よ₀ x .fobj y .commMonoid .+-lunit = lift (homCM _ _ .+-lunit)
よ₀ x .fobj y .commMonoid .+-assoc = lift (homCM _ _ .+-assoc)
よ₀ x .fobj y .commMonoid .+-comm = lift (homCM _ _ .+-comm)
よ₀ x .fmor f .function = yoneda.よ₀ x .fmor f
よ₀ x .fmor f .cmFunc .preserve-ε = lift (comp-bilinear-ε₁ _)
よ₀ x .fmor f .cmFunc .preserve-+ = lift (comp-bilinear₁ _ _ _)
よ₀ x .fmor-cong = yoneda.よ₀ x .fmor-cong
よ₀ x .fmor-id = yoneda.よ₀ x .fmor-id
よ₀ x .fmor-comp = yoneda.よ₀ x .fmor-comp

よ : Functor 𝒞 PSh
よ .fobj = よ₀
よ .fmor f .transf y .function = yoneda.よ .fmor f .transf y
よ .fmor f .transf y .cmFunc .preserve-ε = lift (comp-bilinear-ε₂ _)
よ .fmor f .transf y .cmFunc .preserve-+ = lift (comp-bilinear₂ _ _ _)
よ .fmor f .natural = yoneda.よ .fmor f .natural
よ .fmor-cong f₁≈f₂ .transf-eq = yoneda.よ .fmor-cong f₁≈f₂ .transf-eq
よ .fmor-id .transf-eq = yoneda.よ .fmor-id .transf-eq
よ .fmor-comp f g .transf-eq = yoneda.よ .fmor-comp _ _ .transf-eq

-- TODO: Yoneda lemma

-- TODO: よ preserves limits
