{-# OPTIONS --postfix-projections --prop --safe #-}

-- The glueing embedding preserves μ-types. Discharges the GFμ hypothesis of
-- the conservativity theorem at the Fam instance: the source μ-object is the
-- Fam(𝒞) W-tree, compared under GF against the realised Fam(Gl) W-tree.
--
-- Parameterised over the glued category and the embedding rather than the
-- data they are built from, so checking this file does not rebuild the
-- interpretation; gf-preserves-mu-instance supplies the pieces.

open import Level using (Level; 0ℓ)
open import Data.Nat using () renaming (suc to sucℕ; _+_ to _+ℕ_)
open import Data.Fin using (Fin)
open import categories
  using (Category; HasProducts; HasTerminal; HasExponentials; HasStrongCoproducts;
         setoid→category)
open import prop-setoid using (Setoid)
open import functor using (Functor; HasColimits; functor-preserve-iso; _∘F_; Colimit; NatIso)
open import indexed-family using (Fam; fam→functor; functor→fam; fam→functor-eta)
import fam
import finite-coproducts-from-indexed
open import finite-product-functor using (preserve-chosen-products)
open import polynomial-functor
  using (Preserves-μ; Poly; Poly-map; constant-free; constant-free-go; Poly-map-constant-free-go;
         constant-free-go-Poly-map; #c; #c-Poly-map; consts; consts-Poly-map; _++e_; ++e-map)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; subst to ≡-subst)
import fam-mu-types
import fam-mu-realisation
import fam-presentation
import gf-preserves-mu.constant-free
import gf-preserves-mu.checked

open Functor
open Colimit

module gf-preserves-mu
  {o o' m' e' : Level}
  (𝒞 : Category o 0ℓ 0ℓ)
  (𝒞-terminal : HasTerminal 𝒞)
  (𝒞-products : HasProducts 𝒞)
  (Gl : Category o' m' e')
  (GlT : HasTerminal Gl)
  (GlP : HasProducts Gl)
  (GlE : HasExponentials Gl GlP)
  (GlSC : HasStrongCoproducts Gl GlP)
  (GDC : ∀ (A : Setoid 0ℓ 0ℓ) → HasColimits (setoid→category A) Gl)
  (GF : Functor (fam.CategoryOfFamilies.cat 0ℓ 0ℓ 𝒞) Gl)
  (GF-preserve-products :
     preserve-chosen-products GF (fam.CategoryOfFamilies.products.products 0ℓ 0ℓ 𝒞 𝒞-products) GlP)
  (GF-preserve-coproducts-indexed :
     ∀ (S : Setoid 0ℓ 0ℓ) (D : Functor (setoid→category S) (fam.CategoryOfFamilies.cat 0ℓ 0ℓ 𝒞)) →
     Category.Iso Gl (GDC S (GF ∘F D) .apex)
                     (GF .fobj (fam.CategoryOfFamilies.bigCoproducts 0ℓ 0ℓ 𝒞 S D .apex)))
  (Gl-Mu : polynomial-functor.Interp.HasMu GlT GlP GlSC)
  (Gl-Mu-obj : ∀ {n} (Q : Poly Gl (sucℕ n)) (δ : Fin n → Category.obj Gl) →
     polynomial-functor.Interp.HasMu.μ-obj Gl-Mu Q δ ≡
     fam-mu-realisation.μ-objℰ 0ℓ 0ℓ GDC GlT GlP GlE GlSC Q δ)
  where

  private
    module Glued = Category Gl
    module Sk  = gf-preserves-mu.constant-free 0ℓ 0ℓ 𝒞-terminal 𝒞-products
    module SkGl = gf-preserves-mu.constant-free 0ℓ 0ℓ GlT GlP
    module FMc = fam-mu-types 0ℓ 0ℓ 𝒞-terminal 𝒞-products
    module RGl = fam-mu-realisation 0ℓ 0ℓ GDC GlT GlP GlE GlSC
    module FMg = RGl.FM
    module Pres = fam-presentation 0ℓ 0ℓ {𝒞}
    module Gld = finite-coproducts-from-indexed.derive GDC
    module FamGl = FMg.Fam𝒞
    module Chk = gf-preserves-mu.checked 0ℓ 0ℓ 𝒞-terminal 𝒞-products GlT GlP GF GF-preserve-products
  open RGl using (realise; η)

  module Fam⟨𝒞⟩ = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒞

  Fam⟨𝒞⟩-terminal : HasTerminal Fam⟨𝒞⟩.cat
  Fam⟨𝒞⟩-terminal = Fam⟨𝒞⟩.terminal 𝒞-terminal

  Fam⟨𝒞⟩-products : HasProducts Fam⟨𝒞⟩.cat
  Fam⟨𝒞⟩-products = Fam⟨𝒞⟩.products.products 𝒞-products

  Fam⟨𝒞⟩-strongCoproducts : HasStrongCoproducts Fam⟨𝒞⟩.cat Fam⟨𝒞⟩-products
  Fam⟨𝒞⟩-strongCoproducts = Fam⟨𝒞⟩.products.strongCoproducts 𝒞-products

  Fam⟨𝒞⟩-hasMu : polynomial-functor.Interp.HasMu Fam⟨𝒞⟩-terminal Fam⟨𝒞⟩-products Fam⟨𝒞⟩-strongCoproducts
  Fam⟨𝒞⟩-hasMu = fam-mu-types.hasMu 0ℓ 0ℓ 𝒞-terminal 𝒞-products

  -- Source side of the carrier comparison: GF of a Fam W-tree is the Gl
  -- set-indexed coproduct of the GF-images of its singleton fibres, via the
  -- canonical presentation and GF's preservation of set-indexed coproducts.
  source-iso : (M : Fam⟨𝒞⟩.Obj) →
    Glued.Iso (GF .fobj M) (GDC (M .Fam⟨𝒞⟩.Obj.idx) (GF ∘F Pres.singletons M) .apex)
  source-iso M =
    Glued.Iso-trans
      (Glued.Iso-sym (functor-preserve-iso GF (Pres.present M)))
      (Glued.Iso-sym (GF-preserve-coproducts-indexed (M .Fam⟨𝒞⟩.Obj.idx) (Pres.singletons M)))

  -- The checked presentation of a Fam(𝒞)-object: the Fam(Gl)-family over the
  -- same index setoid, obtained by applying GF to the singleton fibres.
  check : Fam⟨𝒞⟩.Obj → FMg.Obj
  check = Chk.check

  -- Compare GF of a family against the realisation of a Gl-family over the same
  -- index setoid, given a pointwise isomorphism of the fibre diagrams.
  presented-iso : (M : Fam⟨𝒞⟩.Obj) (Nf : Fam (M .Fam⟨𝒞⟩.Obj.idx) Gl) →
                  NatIso (GF ∘F Pres.singletons M) (fam→functor Nf) →
                  Glued.Iso (GF .fobj M) (realise .fobj (record { idx = M .Fam⟨𝒞⟩.Obj.idx ; fam = Nf }))
  presented-iso M Nf α = Glued.Iso-trans (source-iso M) (Gld.∐-iso α)

  -- GF of a family is the realisation of its checked presentation.
  check-iso : (M : Fam⟨𝒞⟩.Obj) → Glued.Iso (GF .fobj M) (realise .fobj (check M))
  check-iso M =
    presented-iso M (functor→fam (GF ∘F Pres.singletons M)) (fam→functor-eta (GF ∘F Pres.singletons M))

  -- check commutes with μ at the constant-free form, as an iso in Fam(Gl):
  -- the shared shapes make the index setoids agree, and the fibres are products
  -- of GF-images compared by tree recursion.
  check-μ : ∀ {n} (P : Poly Fam⟨𝒞⟩.cat (sucℕ n)) (ε : Fin (n +ℕ #c P) → Fam⟨𝒞⟩.Obj) →
            FamGl.Iso (check (FMc.μObj (constant-free P) ε)) (FMg.μObj (constant-free P) (λ i → check (ε i)))
  check-μ P ε = Chk.ChkMu.check-μ-iso P ε

  -- Realised μ-objects along an equality of polynomials.
  μObj-≡-iso : ∀ {k} {Q₁ Q₂ : Poly FMg.cat (sucℕ k)} (e : Q₁ ≡ Q₂) (δ̂ : Fin k → FMg.Obj) →
               Glued.Iso (realise .fobj (FMg.μObj Q₁ δ̂)) (realise .fobj (FMg.μObj Q₂ δ̂))
  μObj-≡-iso ≡-refl δ̂ = Glued.Iso-refl

  obj-≡-iso : ∀ {X Y : Glued.obj} → X ≡ Y → Glued.Iso X Y
  obj-≡-iso ≡-refl = Glued.Iso-refl

  -- GF preserves μ-types: constant-free in Fam(𝒞), carrier comparison, invariance at
  -- the checked-versus-embedded environments, and the realised constant-free in
  -- Fam(Gl), backwards.
  GFμ : Preserves-μ Fam⟨𝒞⟩-terminal Fam⟨𝒞⟩-products Fam⟨𝒞⟩-strongCoproducts
          GlT GlP GlSC Fam⟨𝒞⟩-hasMu Gl-Mu GF
  GFμ {n} P δ =
    Glued.Iso-trans (functor-preserve-iso GF (Sk.constant-free-μ-iso P δ))
    (Glued.Iso-trans (check-iso (FMc.μObj (constant-free P) ε))
    (Glued.Iso-trans (functor-preserve-iso realise (check-μ P ε))
    (Glued.Iso-trans (μObj-≡-iso (≡-sym (Poly-map-constant-free-go η P (λ c → c))) (λ i → check (ε i)))
    (Glued.Iso-trans (RGl.MuInvariance.mu-invariance SKg (RGl.invarianceAt SKg)
                       (λ i → check (ε i)) (λ i → η .fobj (GF .fobj (ε i))) isos)
    (Glued.Iso-trans realised-constant-free
      (obj-≡-iso (≡-sym (Gl-Mu-obj (Poly-map GF P) (λ i → GF .fobj (δ i))))))))))
    where
      ε : Fin (n +ℕ #c P) → Fam⟨𝒞⟩.Obj
      ε = δ ++e consts P

      SKg : Poly Gl (sucℕ (n +ℕ #c P))
      SKg = constant-free P

      isos : ∀ i → Glued.Iso (realise .fobj (check (ε i)))
                             (realise .fobj (η .fobj (GF .fobj (ε i))))
      isos i = Glued.Iso-trans (Glued.Iso-sym (check-iso (ε i)))
                 (Glued.Iso-sym (RGl.realise-η-iso (GF .fobj (ε i))))

      -- The realised constant-free in Fam(Gl), backwards: invariance the embedded
      -- environment onto the extended one, share the constant-free form between P and its
      -- GF-image, and apply the Fam(Gl) constant-free lemma at the image polynomial.
      realised-constant-free : Glued.Iso (RGl.Creal SKg (λ i → η .fobj (GF .fobj (ε i))))
                                    (RGl.μ-objℰ (Poly-map GF P) (λ i → GF .fobj (δ i)))
      realised-constant-free =
        Glued.Iso-trans
          (RGl.MuInvariance.mu-invariance SKg (RGl.invarianceAt SKg)
            (λ i → η .fobj (GF .fobj (ε i))) (δ̂ ++e cs̄)
            (λ i → obj-≡-iso (cong (realise .fobj)
                     (++e-map (λ X → η .fobj (GF .fobj X)) δ (consts P) i))))
        (Glued.Iso-trans (Glued.Iso-sym (μObj-≡-iso constant-free-forms-agree (δ̂ ++e cs̄)))
          (Glued.Iso-sym (functor-preserve-iso realise SkI.constant-free-inst-iso)))
        where
          δ̂ : Fin n → FMg.Obj
          δ̂ i = η .fobj (GF .fobj (δ i))

          cs̄ : Fin (#c P) → FMg.Obj
          cs̄ c = η .fobj (GF .fobj (consts P c))

          P̂ : Poly FMg.cat (sucℕ n)
          P̂ = Poly-map η (Poly-map GF P)

          ι̂ : Fin (#c P̂) → Fin (#c P)
          ι̂ c = ≡-subst Fin (#c-Poly-map GF P) (≡-subst Fin (#c-Poly-map η (Poly-map GF P)) c)

          csok : ∀ c → cs̄ (ι̂ c) ≡ consts P̂ c
          csok c =
            ≡-sym (≡-trans (consts-Poly-map η (Poly-map GF P) c)
              (cong (η .fobj) (consts-Poly-map GF P (≡-subst Fin (#c-Poly-map η (Poly-map GF P)) c))))

          module SkI = SkGl.ConstantFree.Inst δ̂ cs̄ P̂ ι̂ csok

          constant-free-forms-agree : constant-free-go P̂ ι̂ ≡ Poly-map η SKg
          constant-free-forms-agree =
            ≡-trans (constant-free-go-Poly-map η (Poly-map GF P) (λ c → ≡-subst Fin (#c-Poly-map GF P) c))
              (≡-trans (constant-free-go-Poly-map GF P (λ c → c))
                (≡-sym (Poly-map-constant-free-go η P (λ c → c))))
