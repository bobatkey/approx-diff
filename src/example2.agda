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
import functor-cat-products

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
PShGalois-biproducts x y = biproducts
  where open cmon-enriched.cmon+products→biproducts
               PShGalois-cmon
               (HasProducts.getProduct PShGalois-products.products x y)

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
