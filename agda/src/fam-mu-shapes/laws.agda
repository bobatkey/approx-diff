{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Fusion for the initial-algebra laws: reindexing a μ-carrier along a
-- pointwise family agrees with the strong functorial action derived from the
-- HasMu operations. fuse-μ is an instance of the index-level uniqueness law:
-- the reindexing satisfies the algebra square of the action's defining fold
-- (by ReindexInMap and fuse-poly), so the two agree. fuse-poly relates the
-- action's one-level behaviour to pointwise reindexing behind the bridges, by
-- induction on the polynomial; its μ-case recurses into fuse-μ at the
-- extended environments, and the reindex layers collapse by ReindexComp.
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

-- The coercions between the two spellings of an extended environment, as
-- morphism families: identity after matching the index.
module CoeFams {n} (P : Poly-C (suc n)) (δ : Fin n → Obj) (A : Obj) where
  module IS = IX.InMap (λ i → δ i .idx) ∣ P ∣

  ιᴬ' : Fin (suc n) → Setoid os (os ⊔ es)
  ιᴬ' = extend (λ i → δ i .idx) (A .idx)

  ιᴬμ : Fin (suc n) → Setoid os (os ⊔ es)
  ιᴬμ v = extend δ A v .idx

  uncoeF : ∀ v → ιᴬ' v prop-setoid.⇒ ιᴬμ v
  uncoeF zero .func x = x
  uncoeF zero .func-resp-≈ p = p
  uncoeF (suc i) .func x = x
  uncoeF (suc i) .func-resp-≈ p = p

  coeF : ∀ v → ιᴬμ v prop-setoid.⇒ ιᴬ' v
  coeF zero .func x = x
  coeF zero .func-resp-≈ p = p
  coeF (suc i) .func x = x
  coeF (suc i) .func-resp-≈ p = p

-- The label-matched coercions agree pointwise with reindexing along the
-- identity families.
module CoeAgree {n} (ι : Fin n → Setoid os (os ⊔ es))
                {ιA ιB : Fin n → Setoid os (os ⊔ es)} (cF : ∀ v → ιA v prop-setoid.⇒ ιB v)
                (cIx : (l : Setoid os (os ⊔ es) ⊎ Fin n) → Sh.Trees.Ix ιA l → Sh.Trees.Ix ιB l)
                (agree : ∀ v x → Setoid._≈_ (ιB v) (cIx (inj₂ v) x) (cF v .func x))
                (agreeS : ∀ S x → Setoid._≈_ S (cIx (inj₁ S) x) x) where
  open Sh.Shapes n
  module RB = IX.Reindex cF
  module EB = Sh.TreeEq ιB (λ v → Setoid._≈_ (ιB v))

  mutual
    agree-W : ∀ {k} {Q : Sh.Poly (suc k)} {ρ} (w : W Q ρ) (a : Sh.Trees.Assign ιA w) →
              EB.W≈ w w (λ p → cIx (labelW w p) (a p)) (λ p → RB.reindexIx (labelW w p) (a p))
    agree-W {Q = Q} {ρ = ρ} (sup s) a = agree-Sh Q (extend ρ (inj₂ (Sh.mkSort Q ρ))) s a

    agree-Sh : ∀ {k} (Q : Sh.Poly k) (η : Fin k → Fin n ⊎ Sh.Sort n) (s : Shape Q η)
               (a : Sh.Trees.AssignSh ιA Q η s) →
               EB.Sh≈ Q η s s (λ p → cIx (labelSh Q η s p) (a p))
                 (λ p → RB.reindexIx (labelSh Q η s p) (a p))
    agree-Sh (const S) η s a = agreeS S (a tt)
    agree-Sh (var j)   η s a = agree-El (η j) s a
    agree-Sh (P + Q)   η (inj₁ s) a = agree-Sh P η s a
    agree-Sh (P + Q)   η (inj₂ s) a = agree-Sh Q η s a
    agree-Sh (P × Q)   η (s₁ , s₂) a =
      agree-Sh P η s₁ (λ p → a (inj₁ p)) , agree-Sh Q η s₂ (λ p → a (inj₂ p))
    agree-Sh (μ Q')    η s a = agree-W s a

    agree-El : ∀ (r : Fin n ⊎ Sh.Sort n) (s : El r) (a : Sh.Trees.AssignEl ιA r s) →
               EB.El≈ r s s (λ p → cIx (labelEl r s p) (a p))
                 (λ p → RB.reindexIx (labelEl r s p) (a p))
    agree-El (inj₁ v)               s a = agree v (a tt)
    agree-El (inj₂ (Sh.mkSort Q ρ)) w a = agree-W w a

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

      mutual
        clp-W : ∀ {k} {Q̄ : Sh.Poly (suc k)} {ρ̄} (w' : FI.ISs.S'.W Q̄ ρ̄)
                (a' : FI.ISs.Tᵢ.Assign w') →
                FI.ISt.Eᵢ.W≈ w' w'
                  (λ p → RGH.reindexIx (FI.ISs.S'.labelW w' p) (a' p))
                  (λ p → FI.IM.coeIx (FI.ISs.S'.labelW w' p)
                           (RG'.reindexIx (FI.ISs.S'.labelW w' p)
                             (FI.FF.uncoeIx (FI.ISs.S'.labelW w' p)
                               (RH.reindexIx (FI.ISs.S'.labelW w' p) (a' p)))))
        clp-W {Q̄ = Q̄} {ρ̄ = ρ̄} (FI.ISs.S'.sup s') a' =
          clp-Sh Q̄ (extend ρ̄ (inj₂ (Sh.mkSort Q̄ ρ̄))) s' a'

        clp-Sh : ∀ {k} (Q̄ : Sh.Poly k) (η̄ : Fin k → Fin (suc N) ⊎ Sh.Sort (suc N))
                 (s' : FI.ISs.S'.Shape Q̄ η̄) (a' : FI.ISs.Tᵢ.AssignSh Q̄ η̄ s') →
                 FI.ISt.Eᵢ.Sh≈ Q̄ η̄ s' s'
                   (λ p → RGH.reindexIx (FI.ISs.S'.labelSh Q̄ η̄ s' p) (a' p))
                   (λ p → FI.IM.coeIx (FI.ISs.S'.labelSh Q̄ η̄ s' p)
                            (RG'.reindexIx (FI.ISs.S'.labelSh Q̄ η̄ s' p)
                              (FI.FF.uncoeIx (FI.ISs.S'.labelSh Q̄ η̄ s' p)
                                (RH.reindexIx (FI.ISs.S'.labelSh Q̄ η̄ s' p) (a' p)))))
        clp-Sh (const S) η̄ s' a' =
          S .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = a' tt}
        clp-Sh (var j)   η̄ s' a' = clp-El (η̄ j) s' a'
        clp-Sh (Q₁ + Q₂) η̄ (inj₁ s') a' = clp-Sh Q₁ η̄ s' a'
        clp-Sh (Q₁ + Q₂) η̄ (inj₂ s') a' = clp-Sh Q₂ η̄ s' a'
        clp-Sh (Q₁ × Q₂) η̄ (s₁ , s₂) a' =
          clp-Sh Q₁ η̄ s₁ (λ p → a' (inj₁ p)) , clp-Sh Q₂ η̄ s₂ (λ p → a' (inj₂ p))
        clp-Sh (μ Q̄')   η̄ s' a' = clp-W s' a'

        clp-El : ∀ (r : Fin (suc N) ⊎ Sh.Sort (suc N)) (s' : FI.ISs.S'.El r)
                 (a' : FI.ISs.Tᵢ.AssignEl r s') →
                 FI.ISt.Eᵢ.El≈ r s' s'
                   (λ p → RGH.reindexIx (FI.ISs.S'.labelEl r s' p) (a' p))
                   (λ p → FI.IM.coeIx (FI.ISs.S'.labelEl r s' p)
                            (RG'.reindexIx (FI.ISs.S'.labelEl r s' p)
                              (FI.FF.uncoeIx (FI.ISs.S'.labelEl r s' p)
                                (RH.reindexIx (FI.ISs.S'.labelEl r s' p) (a' p)))))
        clp-El (inj₁ zero)    s' a' =
          μObj Q (D .sₜ) .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.sym
            {x = rh zero .func (a' tt)}
            {y = IX.Reindex.reindex {ι = λ v → D .sₛ v .idx} {ι' = λ v → D .sₜ v .idx}
                   (D .gγ γ) {Q = ∣ Q ∣} {ρ = λ i → inj₁ i} (a' tt)}
            (rh0 (a' tt))
        clp-El (inj₁ (suc i)) s' a' =
          D .gγ γ i .func-resp-≈
            (D .sₛ i .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.sym (rh1 i (a' tt)))
        clp-El (inj₂ (Sh.mkSort Q̄ ρ̄)) w' a' = clp-W w' a'

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

      mutual
        clpβ-W : ∀ {k} {Q̄ : Sh.Poly (suc k)} {ρ̄} (w' : IM.I.S'.W Q̄ ρ̄)
                 (a' : Sh.Trees.Assign (λ v → extend δ (μObj P δ) v .idx) w')
                 → FF.EAμ.W≈ w' w'
                     (λ p → RGp.reindexIx (IM.I.S'.labelW w' p) (a' p))
                     (λ p → FF.uncoeIx (IM.I.S'.labelW w' p)
                              (RGβ.reindexIx (IM.I.S'.labelW w' p)
                                (IM.coeIx (IM.I.S'.labelW w' p) (a' p))))
        clpβ-W {Q̄ = Q̄} {ρ̄ = ρ̄} (IM.I.S'.sup s') a' =
          clpβ-Sh Q̄ (extend ρ̄ (inj₂ (Sh.mkSort Q̄ ρ̄))) s' a'

        clpβ-Sh : ∀ {k} (Q̄ : Sh.Poly k) (η̄ : Fin k → Fin (suc n) ⊎ Sh.Sort (suc n))
                  (s' : IM.I.S'.Shape Q̄ η̄)
                  (a' : Sh.Trees.AssignSh (λ v → extend δ (μObj P δ) v .idx) Q̄ η̄ s')
                  → FF.EAμ.Sh≈ Q̄ η̄ s' s'
                      (λ p → RGp.reindexIx (IM.I.S'.labelSh Q̄ η̄ s' p) (a' p))
                      (λ p → FF.uncoeIx (IM.I.S'.labelSh Q̄ η̄ s' p)
                               (RGβ.reindexIx (IM.I.S'.labelSh Q̄ η̄ s' p)
                                 (IM.coeIx (IM.I.S'.labelSh Q̄ η̄ s' p) (a' p))))
        clpβ-Sh (const S) η̄ s' a' =
          S .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = a' tt}
        clpβ-Sh (var j)   η̄ s' a' = clpβ-El (η̄ j) s' a'
        clpβ-Sh (Q₁ + Q₂) η̄ (inj₁ s') a' = clpβ-Sh Q₁ η̄ s' a'
        clpβ-Sh (Q₁ + Q₂) η̄ (inj₂ s') a' = clpβ-Sh Q₂ η̄ s' a'
        clpβ-Sh (Q₁ × Q₂) η̄ (s₁ , s₂) a' =
          clpβ-Sh Q₁ η̄ s₁ (λ p → a' (inj₁ p)) , clpβ-Sh Q₂ η̄ s₂ (λ p → a' (inj₂ p))
        clpβ-Sh (μ Q̄')   η̄ s' a' = clpβ-W s' a'

        clpβ-El : ∀ (r : Fin (suc n) ⊎ Sh.Sort (suc n)) (s' : IM.I.S'.El r)
                  (a' : Sh.Trees.AssignEl (λ v → extend δ (μObj P δ) v .idx) r s')
                  → FF.EAμ.El≈ r s' s'
                      (λ p → RGp.reindexIx (IM.I.S'.labelEl r s' p) (a' p))
                      (λ p → FF.uncoeIx (IM.I.S'.labelEl r s' p)
                               (RGβ.reindexIx (IM.I.S'.labelEl r s' p)
                                 (IM.coeIx (IM.I.S'.labelEl r s' p) (a' p))))
        clpβ-El (inj₁ zero)    s' a' =
          A .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl
            {x = k .idxf .func (γ , a' tt)}
        clpβ-El (inj₁ (suc i)) s' a' =
          δ i .idx .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl {x = a' tt}
        clpβ-El (inj₂ (Sh.mkSort Q̄ ρ̄)) w' a' = clpβ-W w' a'

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
