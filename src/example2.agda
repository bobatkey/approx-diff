{-# OPTIONS --prop --postfix-projections --safe #-}

module example2 where

open import Level using (suc; 0ℓ)

open import categories
  using (Category; opposite;
         HasProducts; HasExponentials; HasBooleans;
         setoid→category)
open import functor using ([_⇒_]; HasLimits)
open import cmon-enriched using (CMonEnriched; FunctorCat-cmon; Biproduct)
open import commutative-monoid-cat using ()
  renaming ( cat to CMon; Obj to CMonObj
           ; limits to CMon-limits
           ; cmon-enriched to CMon-enriched
           ; products to CMon-products
           ; terminal to CMon-terminal)

import grothendieck

open import functor using (Functor)
open import families-functor using (FamF)
open import cmon-yoneda using (よ)

------------------------------------------------------------------------------
-- This is generic over the base category; make it work for any
-- cmon-category with products. Move it all to cmon-yoneda.
import galois
-- import graph-lang

cat = galois.cat -- graph-lang.cat {!!}

PShGalois : Category (suc (suc 0ℓ)) (suc 0ℓ) (suc 0ℓ)
PShGalois = [ opposite cat ⇒ CMon (suc 0ℓ) (suc 0ℓ) ]

PShGalois-limits : (𝒮 : Category (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)) → HasLimits 𝒮 PShGalois
PShGalois-limits 𝒮 = limits
  where open import functor-cat-limits _ _ 𝒮 (CMon-limits (suc 0ℓ) 𝒮)

PShGalois-cmon : CMonEnriched PShGalois
PShGalois-cmon = FunctorCat-cmon _ _ CMon-enriched

import functor-cat-products (opposite cat) (CMon (suc 0ℓ) (suc 0ℓ))
                            CMon-terminal
                            CMon-products
   as PShGalois-products

PShGalois-biproducts : ∀ x y → Biproduct PShGalois-cmon x y
PShGalois-biproducts =
  cmon-enriched.cmon+products→biproducts PShGalois-cmon PShGalois-products.products

------------------------------------------------------------------------------
-- Fam(PSh(Galois)) can now interpret the calculus

module D = grothendieck.CategoryOfFamilies (suc 0ℓ) (suc 0ℓ) PShGalois
module DP = D.products (cmon-enriched.biproducts→products _ PShGalois-biproducts)

D-products : HasProducts D.cat
D-products = DP.products

D-exponentials : HasExponentials D.cat D-products
D-exponentials = exponentials
  where open import fam using (hasSetoidProducts)
        open import families-exponentials (suc 0ℓ) (suc 0ℓ)
                          PShGalois
                          PShGalois-cmon
                          PShGalois-biproducts
                          (hasSetoidProducts _ _ PShGalois
                             λ A → PShGalois-limits (setoid→category A))

D-terminal = D.terminal PShGalois-products.terminal

D-booleans = categories.coproducts→booleans D-terminal DP.strongCoproducts

D-lists = D.lists PShGalois-products.terminal PShGalois-products.products

------------------------------------------------------------------------------
-- First order version where we interpret the basic operations from
-- the signature.

module D-fo = grothendieck.CategoryOfFamilies (suc 0ℓ) (suc 0ℓ) cat

embed : Functor D-fo.cat D.cat
embed = FamF _ _ (よ _ _ cat galois.cmon-enriched)

-- TODO: 'embed' preserves finite products and booleans.  So any
-- signature interpreted in Fam(LatGal) can also be interpreted in
-- Fam(Psh(LatGal)). Then we will be able to interpret the whole
-- higher-order language in the latter category, and then read back
-- the first order LatGal morphism at the end.
