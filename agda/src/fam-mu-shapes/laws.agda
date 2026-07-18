{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Fusion for the initial-algebra laws: reindexing a μ-carrier along a
-- pointwise family agrees with the strong functorial action derived from the
-- HasMu operations. fuse-μ is an instance of the index-level uniqueness law:
-- the reindexing satisfies the algebra square of the action's defining fold
-- (by ReindexInMap and fuse-poly), so the two agree. fuse-poly relates the
-- action's one-level behaviour to pointwise reindexing behind the bridges, by
-- induction on the polynomial; its μ-case recurses into fuse-μ at the
-- extended environments, and the layers collapse pointwise.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import prop using (_,_)
open import prop-setoid using (Setoid)
open import categories using (Category; HasTerminal; HasProducts)
open import indexed-family using (Fam)
import fam-mu-shapes.fold-fam

module fam-mu-shapes.laws {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (CP : HasProducts 𝒞) where

open fam-mu-shapes.fold-fam os es T CP public
open HasMu hasMu using (strong-fmor; strong-μ-fmor; strong-extend-mor)
open prop-setoid._⇒_

private
  ℓF : Level
  ℓF = o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es

-- The data of a fusion instance: an ambient context, two environments, the
-- Fam-morphism family between them, and a per-γ pointwise index family
-- agreeing with it.
record FuseData (N : ℕ) : Set ℓF where
  no-eta-equality
  field
    Γ : Obj
    sₛ sₜ : Fin N → Obj
    fs : ∀ v → Fam𝒞._⇒_ (Fam𝒞-P.prod Γ (sₛ v)) (sₜ v)
    gγ : (γ : Γ .idx .Setoid.Carrier) (v : Fin N) → (sₛ v .idx) prop-setoid.⇒ (sₜ v .idx)
    corr : ∀ γ v x → Setoid._≈_ (sₜ v .idx) (gγ γ v .func x) (fs v .idxf .func (γ , x))

open FuseData

-- Extend a fusion instance under a binder: the fresh entry is the target
-- μ-object on both sides, mapped identically.
ext-data : ∀ {N} (D : FuseData N) (Q : Poly-C (suc N)) → FuseData (suc N)
ext-data D Q .Γ = D .Γ
ext-data D Q .sₛ = extend (D .sₛ) (μObj Q (D .sₜ))
ext-data D Q .sₜ = extend (D .sₜ) (μObj Q (D .sₜ))
ext-data D Q .fs = strong-extend-mor (D .fs) Fam𝒞-P.p₂
ext-data D Q .gγ γ zero = prop-setoid.idS _
ext-data D Q .gγ γ (suc i) = D .gγ γ i
ext-data D Q .corr γ zero x =
  μObj Q (D .sₜ) .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x}
ext-data D Q .corr γ (suc i) x = D .corr γ i x

-- The instance-level bridges and the one-level pipeline of the strong
-- action's defining algebra.
module FuseInst {N} (D : FuseData N) (Q : Poly-C (suc N)) where
  module ISs = IX.InMap (λ v → D .sₛ v .idx) ∣ Q ∣
  module ISt = IX.InMap (λ v → D .sₜ v .idx) ∣ Q ∣
  module FF = FoldFam (D .Γ) (μObj Q (D .sₜ)) Q (D .sₛ)
  module IM = InMapFam Q (D .sₜ)
  module IN = IX.Initiality (λ v → D .sₛ v .idx) (D .Γ .idx) (μObj Q (D .sₜ) .idx) ∣ Q ∣

  fs★ : ∀ v → Fam𝒞._⇒_ (Fam𝒞-P.prod (D .Γ) (extend (D .sₛ) (μObj Q (D .sₜ)) v))
                        (extend (D .sₜ) (μObj Q (D .sₜ)) v)
  fs★ = strong-extend-mor (D .fs) Fam𝒞-P.p₂

  pipe : (R : Poly-C (suc N)) (rh : ∀ v → ISs.ιᵢ v prop-setoid.⇒ FF.F.ι' v)
         (γ : D .Γ .idx .Setoid.Carrier) →
         ISs.Tᵢ.TreeSh ∣ R ∣ IX.params → ISt.Tᵢ.TreeSh ∣ R ∣ IX.params
  pipe R rh γ x =
    IM.coe-treeSh {Q = ∣ R ∣} {η̄ = IX.params}
      (IM.embed-idx R (strong-fmor R fs★ .idxf .func
        (γ , FF.unembed-idx R (FF.uncoe-treeSh ∣ R ∣ IX.params
               (IX.Reindex.reindexSh rh {Q = ∣ R ∣} {η = IX.params} x)))))

mutual
  fuse-μ : ∀ {N} (D : FuseData N) (Q : Poly-C (suc N)) (γ : D .Γ .idx .Setoid.Carrier)
           (t : μObj Q (D .sₛ) .idx .Setoid.Carrier) →
           Setoid._≈_ (μObj Q (D .sₜ) .idx)
             (IX.Reindex.reindex {ι = λ v → D .sₛ v .idx} {ι' = λ v → D .sₜ v .idx}
                (D .gγ γ) {Q = ∣ Q ∣} {ρ = λ i → inj₁ i} t)
             (strong-μ-fmor Q (D .fs) .idxf .func (γ , t))
  fuse-μ {N} D Q γ t = FI.IN.η ALGIx ALGIxR h hR hβ γ t
    where
      module FI = FuseInst D Q
      module Yμ = prop-setoid.IsEquivalence (μObj Q (D .sₜ) .idx .Setoid.isEquivalence)

      ALG : Fam𝒞._⇒_ (Fam𝒞-P.prod (D .Γ) (fobj μObj Q (extend (D .sₛ) (μObj Q (D .sₜ)))))
                     (μObj Q (D .sₜ))
      ALG = Fam𝒞._∘_ (hasMu .HasMu.inMap Q (D .sₜ)) (strong-fmor Q FI.fs★)

      ALGIx = FI.FF.algIx ALG
      ALGIxR = FI.FF.algIx-resp ALG

      h : D .Γ .idx .Setoid.Carrier → μObj Q (D .sₛ) .idx .Setoid.Carrier →
          μObj Q (D .sₜ) .idx .Setoid.Carrier
      h γ' t' = IX.Reindex.reindex {ι = λ v → D .sₛ v .idx} {ι' = λ v → D .sₜ v .idx}
                  (D .gγ γ') {Q = ∣ Q ∣} {ρ = λ i → inj₁ i} t'

      hR : ∀ {γ₁ γ₂} (γ≈ : Setoid._≈_ (D .Γ .idx) γ₁ γ₂)
           {t₁ t₂ : μObj Q (D .sₛ) .idx .Setoid.Carrier} →
           FI.IN.I.E.Tree≈ t₁ t₂ → Setoid._≈_ (μObj Q (D .sₜ) .idx) (h γ₁ t₁) (h γ₂ t₂)
      hR {γ₁} {γ₂} γ≈ {t₁} {t₂} p =
        IX.ReindexCong.reindex-W-cong (D .gγ γ₁) (D .gγ γ₂)
          (λ v x →
            let module Sv = prop-setoid.IsEquivalence (D .sₜ v .idx .Setoid.isEquivalence) in
            Sv.trans (D .corr γ₁ v x)
              (Sv.trans (D .fs v .idxf .func-resp-≈
                 (γ≈ , D .sₛ v .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x}))
                (Sv.sym (D .corr γ₂ v x))))
          {w₁ = proj₁ t₁} {w₂ = proj₁ t₂} p

      hβ : (γ' : D .Γ .idx .Setoid.Carrier) (t' : FI.ISs.Tᵢ.TreeSh ∣ Q ∣ IX.params) →
           Setoid._≈_ (μObj Q (D .sₜ) .idx)
             (h γ' (FI.ISs.inMap t'))
             (ALGIx γ' (IX.Reindex.reindexSh (FI.IN.hg ALGIx ALGIxR h hR γ')
                         {Q = ∣ Q ∣} {η = IX.params} t'))
      hβ γ' t' =
        Yμ.trans
          (IX.ReindexInMap.reindex-inMap (D .gγ γ') ∣ Q ∣ t')
          (FI.ISt.in-shape-resp ∣ Q ∣ IX.fbase
            (fuse-poly D Q Q γ' (FI.IN.hg ALGIx ALGIxR h hR γ')
              (λ t'' → Yμ.refl {x = h γ' t''})
              (λ i x → D .sₛ i .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x})
              t'))

  fuse-poly : ∀ {N} (D : FuseData N) (Q : Poly-C (suc N)) (R : Poly-C (suc N))
              (γ : D .Γ .idx .Setoid.Carrier)
              (rh : ∀ v → FuseInst.ISs.ιᵢ D Q v prop-setoid.⇒ FuseInst.FF.F.ι' D Q v)
              (rh0 : ∀ t'' → Setoid._≈_ (μObj Q (D .sₜ) .idx) (rh zero .func t'')
                       (IX.Reindex.reindex {ι = λ v → D .sₛ v .idx} {ι' = λ v → D .sₜ v .idx}
                          (D .gγ γ) {Q = ∣ Q ∣} {ρ = λ i → inj₁ i} t''))
              (rh1 : ∀ i x → Setoid._≈_ (D .sₛ i .idx) (rh (suc i) .func x) x)
              (x : FuseInst.ISs.Tᵢ.TreeSh D Q ∣ R ∣ IX.params) →
              FuseInst.ISt.Eᵢ.Sh≈ D Q ∣ R ∣ IX.params
                (proj₁ (IX.Reindex.reindexSh (IX.ReindexInMap.ĝ (D .gγ γ) ∣ Q ∣)
                          {Q = ∣ R ∣} {η = IX.params} x))
                (proj₁ (FuseInst.pipe D Q R rh γ x))
                (proj₂ (IX.Reindex.reindexSh (IX.ReindexInMap.ĝ (D .gγ γ) ∣ Q ∣)
                          {Q = ∣ R ∣} {η = IX.params} x))
                (proj₂ (FuseInst.pipe D Q R rh γ x))
  fuse-poly D Q (const A') γ rh rh0 rh1 (s , a) =
    A' .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = a tt}
  fuse-poly D Q (var zero) γ rh rh0 rh1 (s , a) =
    μObj Q (D .sₜ) .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.sym
      {x = rh zero .func (a tt)}
      {y = IX.Reindex.reindex {ι = λ v → D .sₛ v .idx} {ι' = λ v → D .sₜ v .idx}
             (D .gγ γ) {Q = ∣ Q ∣} {ρ = λ i → inj₁ i} (a tt)}
      (rh0 (a tt))
  fuse-poly D Q (var (suc i)) γ rh rh0 rh1 (s , a) =
    let module Sv = prop-setoid.IsEquivalence (D .sₜ i .idx .Setoid.isEquivalence) in
    Sv.trans (D .corr γ i (a tt))
      (D .fs i .idxf .func-resp-≈
        (D .Γ .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl
        , D .sₛ i .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.sym (rh1 i (a tt))))
  fuse-poly D Q (R₁ + R₂) γ rh rh0 rh1 (inj₁ s , a) = fuse-poly D Q R₁ γ rh rh0 rh1 (s , a)
  fuse-poly D Q (R₁ + R₂) γ rh rh0 rh1 (inj₂ s , a) = fuse-poly D Q R₂ γ rh rh0 rh1 (s , a)
  fuse-poly D Q (R₁ × R₂) γ rh rh0 rh1 ((s₁ , s₂) , a) =
    fuse-poly D Q R₁ γ rh rh0 rh1 (s₁ , λ p → a (inj₁ p)) ,
    fuse-poly D Q R₂ γ rh rh0 rh1 (s₂ , λ p → a (inj₂ p))
  fuse-poly {N} D Q (μ Q'') γ rh rh0 rh1 (w , a) =
    EqIt.W≈-trans {w₁ = w} {w₂ = w} {w₃ = proj₁ (FuseInst.pipe D Q (μ Q'') rh γ (w , a))}
      (clp-W w a)
      (FI.IM.coe-W-resp {w₁ = w} {w₂ = proj₁ (FuseInst.pipe D Q (μ Q'') rh γ (w , a))}
        (fuse-μ (ext-data D Q) Q'' γ (w , λ p →
          FI.FF.uncoeIx (FI.ISs.S'.labelW w p)
            (IX.Reindex.reindexIx rh (FI.ISs.S'.labelW w p) (a p)))))
    where
      module FI = FuseInst D Q
      module EqIt = FI.ISt.Eᵢ.Equiv
        (λ v x → FI.ISt.ιᵢ v .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x})
        (λ v p → FI.ISt.ιᵢ v .Setoid.isEquivalence .prop-setoid.IsEquivalence.sym p)
        (λ v p q → FI.ISt.ιᵢ v .Setoid.isEquivalence .prop-setoid.IsEquivalence.trans p q)
      module RGH = IX.Reindex (IX.ReindexInMap.ĝ (D .gγ γ) ∣ Q ∣)
      module RG' = IX.Reindex (ext-data D Q .gγ γ)
      module RH = IX.Reindex rh

      hSf : ∀ S x → Setoid._≈_ S x x
      hSf S x = S .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x}

      hVf : ∀ v x → Setoid._≈_ (FI.ISt.ιᵢ v)
              (RGH.reindexIx (inj₂ v) x)
              (FI.IM.coeIx (inj₂ v) (RG'.reindexIx (inj₂ v) (FI.FF.uncoeIx (inj₂ v) (RH.reindexIx (inj₂ v) x))))
      hVf zero x =
        μObj Q (D .sₜ) .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.sym
          {x = rh zero .func x}
          {y = IX.Reindex.reindex {ι = λ v → D .sₛ v .idx} {ι' = λ v → D .sₜ v .idx}
                 (D .gγ γ) {Q = ∣ Q ∣} {ρ = λ i → inj₁ i} x}
          (rh0 x)
      hVf (suc i) x =
        D .gγ γ i .func-resp-≈
          (D .sₛ i .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.sym (rh1 i x))

      module CLP = IX.Pointwise
        (λ l x → RGH.reindexIx l x)
        (λ l x → FI.IM.coeIx l (RG'.reindexIx l (FI.FF.uncoeIx l (RH.reindexIx l x))))
        hSf hVf

      clp-W = CLP.agree-W

------------------------------------------------------------------------------
-- The index half of the β law: the strong action of the fold agrees with the
-- fold's own translation behind the bridges. The fusion data is the
-- Initiality g-family at the actual fold, so the correspondence holds by
-- reflexivity; the μ-case is fuse-μ plus an all-reflexivity collapse of the
-- three bridge layers.
------------------------------------------------------------------------------
module KLaw {n} (Γ A : Obj) (P : Poly-C (suc n)) (δ : Fin n → Obj)
            (k : Fam𝒞._⇒_ (Fam𝒞-P.prod Γ (μObj P δ)) A) where
  module FF = FoldFam Γ A P δ
  module IM = InMapFam P δ
  module IN = IX.Initiality (λ i → δ i .idx) (Γ .idx) (A .idx) ∣ P ∣

  fsβ : ∀ v → Fam𝒞._⇒_ (Fam𝒞-P.prod Γ (extend δ (μObj P δ) v)) (extend δ A v)
  fsβ = strong-extend-mor (λ i → Fam𝒞-P.p₂) k

  kγ : (γ : Γ .idx .Setoid.Carrier) → μObj P δ .idx prop-setoid.⇒ A .idx
  kγ γ .func t = k .idxf .func (γ , t)
  kγ γ .func-resp-≈ p =
    k .idxf .func-resp-≈
      (Γ .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl , p)

  Dβ : FuseData (suc n)
  Dβ .FuseData.Γ = Γ
  Dβ .sₛ = extend δ (μObj P δ)
  Dβ .sₜ = extend δ A
  Dβ .fs = fsβ
  Dβ .gγ γ zero = kγ γ
  Dβ .gγ γ (suc i) = prop-setoid.idS _
  Dβ .corr γ zero x =
    A .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl
      {x = k .idxf .func (γ , x)}
  Dβ .corr γ (suc i) x =
    δ i .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x}

  -- The same family at the setoid-extended spelling, for the bridges.
  gI : (γ : Γ .idx .Setoid.Carrier) → ∀ v → IM.I.ιᵢ v prop-setoid.⇒ FF.F.ι' v
  gI γ zero = kγ γ
  gI γ (suc i) = prop-setoid.idS _

  β-idx : (R : Poly-C (suc n)) (γ : Γ .idx .Setoid.Carrier)
          (m : fobj μObj R (extend δ (μObj P δ)) .idx .Setoid.Carrier) →
          Setoid._≈_ (fobj μObj R (extend δ A) .idx)
            (strong-fmor R fsβ .idxf .func (γ , m))
            (FF.unembed-idx R (FF.uncoe-treeSh ∣ R ∣ IX.params
              (IX.Reindex.reindexSh (gI γ) {Q = ∣ R ∣} {η = IX.params}
                (IM.coe-treeSh {Q = ∣ R ∣} {η̄ = IX.params} (IM.embed-idx R m)))))
  β-idx (const A') γ m = A' .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = m}
  β-idx (var zero) γ m =
    A .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl
      {x = k .idxf .func (γ , m)}
  β-idx (var (suc i)) γ m =
    δ i .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = m}
  β-idx (R₁ + R₂) γ (inj₁ m) = β-idx R₁ γ m
  β-idx (R₁ + R₂) γ (inj₂ m) = β-idx R₂ γ m
  β-idx (R₁ × R₂) γ (m₁ , m₂) = β-idx R₁ γ m₁ , β-idx R₂ γ m₂
  β-idx (μ Q'') γ m =
    EqAμ.W≈-trans
      {w₁ = proj₁ (strong-μ-fmor Q'' fsβ .idxf .func (γ , m))}
      {w₂ = proj₁ m} {w₃ = proj₁ m}
      (EqAμ.W≈-sym {w₁ = proj₁ m}
        {w₂ = proj₁ (strong-μ-fmor Q'' fsβ .idxf .func (γ , m))}
        (fuse-μ Dβ Q'' γ m))
      (clpβ-W (proj₁ m) (proj₂ m))
    where
      module EqAμ = FF.EAμ.Equiv
        (λ v x → FF.ιᴬμ v .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x})
        (λ v p → FF.ιᴬμ v .Setoid.isEquivalence .prop-setoid.IsEquivalence.sym p)
        (λ v p q → FF.ιᴬμ v .Setoid.isEquivalence .prop-setoid.IsEquivalence.trans p q)
      module RGβ = IX.Reindex (gI γ)
      module RGp = IX.Reindex (Dβ .gγ γ)

      hSb : ∀ S x → Setoid._≈_ S x x
      hSb S x = S .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x}

      hVb : ∀ v x → Setoid._≈_ (FF.ιᴬμ v)
              (RGp.reindexIx (inj₂ v) x)
              (FF.uncoeIx (inj₂ v) (RGβ.reindexIx (inj₂ v) (IM.coeIx (inj₂ v) x)))
      hVb zero x =
        A .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl
          {x = k .idxf .func (γ , x)}
      hVb (suc i) x =
        δ i .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x}

      module CLPB = IX.Pointwise
        (λ l x → RGp.reindexIx l x)
        (λ l x → FF.uncoeIx l (RGβ.reindexIx l (IM.coeIx l x)))
        hSb hVb

      clpβ-W = CLPB.agree-W

module BetaLaw {n} (Γ A : Obj) (P : Poly-C (suc n)) (δ : Fin n → Obj)
               (alg : Fam𝒞._⇒_ (Fam𝒞-P.prod Γ (fobj μObj P (extend δ A))) A) where
  module FF = FoldFam Γ A P δ
  module IM = InMapFam P δ
  module IN = IX.Initiality (λ i → δ i .idx) (Γ .idx) (A .idx) ∣ P ∣

  algIx = FF.algIx alg
  algIxR = FF.algIx-resp alg

  module K = KLaw Γ A P δ (FF.foldMor alg)

  fsβ = K.fsβ

  -- The index content of ⦅⦆-β: fold after the algebra map equals the algebra
  -- after the strong action of the fold, with variance in both the context
  -- and the argument. Initiality.β turns the left side into the algebra at
  -- the reindexed unfolding; β-idx turns that into the strong action.
  ⦅⦆-β-idx : ∀ {γ₁ γ₂ : Γ .idx .Setoid.Carrier}
             {m₁ m₂ : fobj μObj P (extend δ (μObj P δ)) .idx .Setoid.Carrier}
             (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂)
             (m≈ : Setoid._≈_ (fobj μObj P (extend δ (μObj P δ)) .idx) m₁ m₂) →
             Setoid._≈_ (A .idx)
               (FF.F.fold algIx γ₁
                 (proj₁ (IM.I.inMap (IM.coe-treeSh {Q = ∣ P ∣} {η̄ = IX.params} (IM.embed-idx P m₁))))
                 (proj₂ (IM.I.inMap (IM.coe-treeSh {Q = ∣ P ∣} {η̄ = IX.params} (IM.embed-idx P m₁)))))
               (alg .idxf .func (γ₂ , strong-fmor P fsβ .idxf .func (γ₂ , m₂)))
  ⦅⦆-β-idx {γ₁} {γ₂} {m₁} {m₂} γ≈ m≈ =
    AE.trans (IN.β algIx algIxR γ₁ t̂₁)
      (AE.trans (alg .idxf .func-resp-≈ (ΓE.refl {x = γ₁} , famStep))
        (AE.trans (alg .idxf .func-resp-≈ (ΓE.refl {x = γ₁} , FE.sym (K.β-idx P γ₁ m₁)))
          (alg .idxf .func-resp-≈ (γ≈ , strong-fmor P fsβ .idxf .func-resp-≈ (γ≈ , m≈)))))
    where
      module AE = prop-setoid.IsEquivalence (A .idx .Setoid.isEquivalence)
      module ΓE = prop-setoid.IsEquivalence (Γ .idx .Setoid.isEquivalence)
      module FE = prop-setoid.IsEquivalence (fobj μObj P (extend δ A) .idx .Setoid.isEquivalence)

      t̂₁ = IM.coe-treeSh {Q = ∣ P ∣} {η̄ = IX.params} (IM.embed-idx P m₁)

      module EqI = IM.I.Eᵢ.Equiv
        (λ v x → IM.I.ιᵢ v .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x})
        (λ v p → IM.I.ιᵢ v .Setoid.isEquivalence .prop-setoid.IsEquivalence.sym p)
        (λ v p q → IM.I.ιᵢ v .Setoid.isEquivalence .prop-setoid.IsEquivalence.trans p q)

      g≈pt : ∀ v x → Setoid._≈_ (FF.F.ι' v) (IN.g algIx algIxR γ₁ v .func x) (K.gI γ₁ v .func x)
      g≈pt zero x = AE.refl {x = FF.F.fold algIx γ₁ (proj₁ x) (proj₂ x)}
      g≈pt (suc i) x = δ i .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x}

      famStep = FF.unembed-resp P (FF.uncoe-Sh-resp ∣ P ∣ IX.params
        (IX.ReindexCong.reindex-Sh-cong (IN.g algIx algIxR γ₁) (K.gI γ₁) g≈pt
          ∣ P ∣ IX.params (EqI.Sh≈-refl ∣ P ∣ IX.params (proj₁ t̂₁) (proj₂ t̂₁))))

------------------------------------------------------------------------------
-- Round trip through the bridges: unembedding a tree-form unfolding into
-- fobj's structure and embedding it back is the identity up to tree equality.
-- Leaf-refl; the inner-μ case collapses the two pointwise coercions.
------------------------------------------------------------------------------
module RoundTrip {n} (Γ : Obj) (P : Poly-C (suc n)) (δ : Fin n → Obj) where
  module FFμ = FoldFam Γ (μObj P δ) P δ
  module IM = InMapFam P δ

  private
    module EqI = IM.I.Eᵢ.Equiv
      (λ v x → IM.I.ιᵢ v .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x})
      (λ v p → IM.I.ιᵢ v .Setoid.isEquivalence .prop-setoid.IsEquivalence.sym p)
      (λ v p q → IM.I.ιᵢ v .Setoid.isEquivalence .prop-setoid.IsEquivalence.trans p q)

  private
    hSr : ∀ (S : Setoid os (os ⊔ es)) x → Setoid._≈_ S x x
    hSr S x = S .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x}

    hVr : ∀ v x → Setoid._≈_ (IM.I.ιᵢ v)
            (IM.coeIx (inj₂ v) (FFμ.uncoeIx (inj₂ v) x)) x
    hVr zero x =
      IM.I.TreeSetoid .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x}
    hVr (suc i) x =
      δ i .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x}

  module RTP = IX.Pointwise
    (λ l x → IM.coeIx l (FFμ.uncoeIx l x)) (λ l x → x) hSr hVr

  rtμ-W = RTP.agree-W

  rt : (R : Poly-C (suc n)) (x : IM.I.Tᵢ.TreeSh ∣ R ∣ IX.params) →
       IM.I.Eᵢ.Sh≈ ∣ R ∣ IX.params
         (proj₁ (IM.coe-treeSh {Q = ∣ R ∣} {η̄ = IX.params}
           (IM.embed-idx R (FFμ.unembed-idx R (FFμ.uncoe-treeSh ∣ R ∣ IX.params x)))))
         (proj₁ x)
         (proj₂ (IM.coe-treeSh {Q = ∣ R ∣} {η̄ = IX.params}
           (IM.embed-idx R (FFμ.unembed-idx R (FFμ.uncoe-treeSh ∣ R ∣ IX.params x)))))
         (proj₂ x)
  rt (const A') (s , a) =
    A' .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = a tt}
  rt (var zero) (s , a) =
    IM.I.TreeSetoid .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = a tt}
  rt (var (suc i)) (s , a) =
    δ i .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = a tt}
  rt (R₁ + R₂) (inj₁ s , a) = rt R₁ (s , a)
  rt (R₁ + R₂) (inj₂ s , a) = rt R₂ (s , a)
  rt (R₁ × R₂) ((s₁ , s₂) , a) =
    rt R₁ (s₁ , λ p → a (inj₁ p)) , rt R₂ (s₂ , λ p → a (inj₂ p))
  rt (μ Q'') (w , a) = rtμ-W w a

------------------------------------------------------------------------------
-- The index half of the η law: any h satisfying the β square agrees with the
-- fold. The square is transported through the round trip so the index-level
-- uniqueness law applies, with one ReindexCong step crossing from KLaw's
-- family to the uniqueness law's own.
------------------------------------------------------------------------------
module EtaLaw {n} (Γ A : Obj) (P : Poly-C (suc n)) (δ : Fin n → Obj)
              (alg : Fam𝒞._⇒_ (Fam𝒞-P.prod Γ (fobj μObj P (extend δ A))) A)
              (h : Fam𝒞._⇒_ (Fam𝒞-P.prod Γ (μObj P δ)) A) where
  module FF = FoldFam Γ A P δ
  module IM = InMapFam P δ
  module IN = IX.Initiality (λ i → δ i .idx) (Γ .idx) (A .idx) ∣ P ∣
  module K = KLaw Γ A P δ h
  module RT = RoundTrip Γ P δ

  algIx = FF.algIx alg
  algIxR = FF.algIx-resp alg

  hcur : (γ : Γ .idx .Setoid.Carrier) → μObj P δ .idx .Setoid.Carrier → A .idx .Setoid.Carrier
  hcur γ t = h .idxf .func (γ , t)

  hR : ∀ {γ₁ γ₂} (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂) {t₁ t₂ : μObj P δ .idx .Setoid.Carrier} →
       IN.I.E.Tree≈ t₁ t₂ → Setoid._≈_ (A .idx) (hcur γ₁ t₁) (hcur γ₂ t₂)
  hR γ≈ p = h .idxf .func-resp-≈ (γ≈ , p)

  module _ (hyp : ∀ (γ : Γ .idx .Setoid.Carrier)
                  (m : fobj μObj P (extend δ (μObj P δ)) .idx .Setoid.Carrier) →
                  Setoid._≈_ (A .idx)
                    (h .idxf .func (γ , IM.I.inMap (IM.coe-treeSh {Q = ∣ P ∣} {η̄ = IX.params}
                                                     (IM.embed-idx P m))))
                    (alg .idxf .func (γ , strong-fmor P K.fsβ .idxf .func (γ , m)))) where

    private
      module AE = prop-setoid.IsEquivalence (A .idx .Setoid.isEquivalence)
      module ΓE = prop-setoid.IsEquivalence (Γ .idx .Setoid.isEquivalence)
      module EqI = IM.I.Eᵢ.Equiv
        (λ v x → IM.I.ιᵢ v .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x})
        (λ v p → IM.I.ιᵢ v .Setoid.isEquivalence .prop-setoid.IsEquivalence.sym p)
        (λ v p q → IM.I.ιᵢ v .Setoid.isEquivalence .prop-setoid.IsEquivalence.trans p q)

    h-β : (γ : Γ .idx .Setoid.Carrier) (t̂ : IM.I.Tᵢ.TreeSh ∣ P ∣ IX.params) →
          Setoid._≈_ (A .idx)
            (hcur γ (IM.I.inMap t̂))
            (algIx γ (IX.Reindex.reindexSh (IN.hg algIx algIxR hcur hR γ)
                       {Q = ∣ P ∣} {η = IX.params} t̂))
    h-β γ t̂ =
      AE.trans (h .idxf .func-resp-≈
          (ΓE.refl {x = γ}
          , IM.I.in-shape-resp ∣ P ∣ IX.fbase
              (EqI.Sh≈-sym ∣ P ∣ IX.params (RT.rt P t̂))))
        (AE.trans (hyp γ m̂)
          (AE.trans (alg .idxf .func-resp-≈ (ΓE.refl {x = γ} , K.β-idx P γ m̂))
            (alg .idxf .func-resp-≈ (ΓE.refl {x = γ} , famStep))))
      where
        m̂ = RT.FFμ.unembed-idx P (RT.FFμ.uncoe-treeSh ∣ P ∣ IX.params t̂)

        g≈pt : ∀ v x → Setoid._≈_ (FF.F.ι' v) (K.gI γ v .func x)
                 (IN.hg algIx algIxR hcur hR γ v .func x)
        g≈pt zero x = AE.refl {x = h .idxf .func (γ , x)}
        g≈pt (suc i) x = δ i .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = x}

        famStep = FF.unembed-resp P (FF.uncoe-Sh-resp ∣ P ∣ IX.params
          (IX.ReindexCong.reindex-Sh-cong (K.gI γ) (IN.hg algIx algIxR hcur hR γ) g≈pt
            ∣ P ∣ IX.params (RT.rt P t̂)))

    ⦅⦆-η-idx : ∀ {γ₁ γ₂ : Γ .idx .Setoid.Carrier} {t₁ t₂ : μObj P δ .idx .Setoid.Carrier}
               (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂) (t≈ : IN.I.E.Tree≈ t₁ t₂) →
               Setoid._≈_ (A .idx)
                 (h .idxf .func (γ₁ , t₁))
                 (FF.F.fold algIx γ₂ (proj₁ t₂) (proj₂ t₂))
    ⦅⦆-η-idx {γ₁} {γ₂} {t₁} {t₂} γ≈ t≈ =
      AE.trans (IN.η algIx algIxR hcur hR h-β γ₁ t₁)
        (FF.F.fold-resp algIx algIxR γ≈ {w₁ = proj₁ t₁} {w₂ = proj₁ t₂} t≈)

------------------------------------------------------------------------------
-- The fibre action of a pointwise environment family, in an ambient context:
-- constant positions are untouched, parameter positions map by the supplied
-- fibre morphisms, the shape and product structure are left fixed.
------------------------------------------------------------------------------
module FibreReindexS {N} (Γ : Obj) {ιA ιB : Fin N → Setoid os (os ⊔ es)}
                     {δfA : ∀ v → Fam (ιA v) 𝒞} {δfB : ∀ v → Fam (ιB v) 𝒞}
                     (g : ∀ v → ιA v prop-setoid.⇒ ιB v)
                     (γ : Γ .idx .Setoid.Carrier)
                     (gf : ∀ v (x : ιA v .Setoid.Carrier) →
                           prod (Γ .fam .fm γ) (δfA v .fm x) ⇒ δfB v .fm (g v .func x)) where
  module FA = Fibre ιA δfA
  module FB = Fibre ιB δfB
  module Rg = IX.Reindex g

  mutual
    rf-W : ∀ {k} {Q : Poly-C (suc k)} {ρ̄} (d : ∀ v → Decos.DecoAssign N (ρ̄ v))
           (w : Sh.Shapes.W N ∣ Q ∣ ρ̄) (a : Sh.Trees.Assign ιA w) →
           prod (Γ .fam .fm γ) (FA.fib Q d w a) ⇒
             FB.fib Q d w (λ p → Rg.reindexIx (Sh.Shapes.labelW N w p) (a p))
    rf-W {Q = Q} d (Sh.Shapes.sup s) a = rf-Sh Q (FA.deco-ext Q d) s a

    rf-Sh : ∀ {j} (Q : Poly-C j) {η̄} (d : ∀ v → Decos.DecoAssign N (η̄ v))
            (s : Sh.Shapes.Shape N ∣ Q ∣ η̄) (a : Sh.Trees.AssignSh ιA ∣ Q ∣ η̄ s) →
            prod (Γ .fam .fm γ) (FA.fib-shape Q d s a) ⇒
              FB.fib-shape Q d s (λ p → Rg.reindexIx (Sh.Shapes.labelSh N ∣ Q ∣ η̄ s p) (a p))
    rf-Sh (const A') d s a = p₂
    rf-Sh (var j)    d s a = rf-El _ (d j) s a
    rf-Sh (Q₁ + Q₂)  d (inj₁ s) a = rf-Sh Q₁ d s a
    rf-Sh (Q₁ + Q₂)  d (inj₂ s) a = rf-Sh Q₂ d s a
    rf-Sh (Q₁ × Q₂)  d (s₁ , s₂) a =
      strong-prod-m (rf-Sh Q₁ d s₁ (λ p → a (inj₁ p))) (rf-Sh Q₂ d s₂ (λ p → a (inj₂ p)))
    rf-Sh (μ Q')     d s a = rf-W d s a

    rf-El : ∀ (r : Fin N ⊎ Sh.Sort N) (dr : Decos.DecoAssign N r)
            (s : Sh.Shapes.El N r) (a : Sh.Trees.AssignEl ιA r s) →
            prod (Γ .fam .fm γ) (FA.fib-el r dr s a) ⇒
              FB.fib-el r dr s (λ p → Rg.reindexIx (Sh.Shapes.labelEl N r s p) (a p))
    rf-El (inj₁ v)            _ s a = gf v (a tt)
    rf-El (inj₂ _) (Decos.mkDeco Q ρd) w a = rf-W ρd w a

------------------------------------------------------------------------------
-- Fibre side of the fusion theorem: the pointwise fibre action along the
-- fusion family, transported along the index-level fusion, equals the strong
-- action's fibre part. Direct tree induction; the transported proofs are
-- Prop-valued, so only their endpoints matter.
------------------------------------------------------------------------------
module FuseFam {N} (D : FuseData N) (Q : Poly-C (suc N)) (γ : D .Γ .idx .Setoid.Carrier) where
  module FI = FuseInst D Q

  ALG : Fam𝒞._⇒_ (Fam𝒞-P.prod (D .Γ) (fobj μObj Q (extend (D .sₛ) (μObj Q (D .sₜ)))))
                 (μObj Q (D .sₜ))
  ALG = Fam𝒞._∘_ (hasMu .HasMu.inMap Q (D .sₜ)) (strong-fmor Q FI.fs★)

  -- The fibre part of the fusion family: the Fam-morphism's fibre map,
  -- transported to sit over the pointwise index family.
  gfD : ∀ v (x : D .sₛ v .idx .Setoid.Carrier) →
        prod (D .Γ .fam .fm γ) (D .sₛ v .fam .fm x) ⇒ D .sₜ v .fam .fm (D .gγ γ v .func x)
  gfD v x =
    D .sₜ v .fam .subst
      (D .sₜ v .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.sym (D .corr γ v x))
      ∘ D .fs v .famf .transf (γ , x)

  module RFμ = FibreReindexS (D .Γ) {ιA = λ v → D .sₛ v .idx} {ιB = λ v → D .sₜ v .idx}
                 {δfA = λ v → D .sₛ v .fam} {δfB = λ v → D .sₜ v .fam}
                 (D .gγ γ) γ gfD

  fuse-fam-μ : (w : Sh.Shapes.W N ∣ Q ∣ (λ i → inj₁ i))
               (a : Sh.Trees.Assign (λ v → D .sₛ v .idx) w) →
               (μObj Q (D .sₜ) .fam .subst
                  {x = IX.Reindex.reindex {ι = λ v → D .sₛ v .idx} {ι' = λ v → D .sₜ v .idx}
                         (D .gγ γ) {Q = ∣ Q ∣} {ρ = λ i → inj₁ i} (w , a)}
                  {y = strong-μ-fmor Q (D .fs) .idxf .func (γ , (w , a))}
                  (fuse-μ D Q γ (w , a))
                ∘ RFμ.rf-W (λ v → lift tt) w a)
                 ≈ strong-μ-fmor Q (D .fs) .famf .transf (γ , (w , a))
  fuse-fam-μ w a = {!!}
