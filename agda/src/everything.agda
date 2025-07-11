{-# OPTIONS --prop --postfix-projections --safe #-}

module everything where

-- Examples from from Section 1.1 and Section 4.3.
--
-- This formalises Example 1.1 and Section 4.3, part (2), with binary
-- approximated numbers, and Section 4.3, part (3), with quantitative
-- approximated numbers.
--
-- We have not yet formalised the CBN translation in Section 4.4, but
-- intend to do so for a final version.
import example

-- Proof from Section 2.2 (Theorem 2.3) that CM (category of bounded
-- meet semilattices and conditionally multiplicative functions) is
-- bicartesian closed. We have not yet formalised Theorem 2.14 on
-- bicartesian-ness of L-posets and stable functions.
import bounded-meet

-- Proof from section 3.2 (Theorem 3.6) that Fam(C) is a cartesian
-- closed if C has biproducts and all small products (Lucatelli Nunes
-- and Vákár 2023).
import fam-exponentials

-- Construction of the interpretation of the higher-order language in
-- Section 4
import ho-model

-- Proofs from Section 5 "Definability"
--
-- (1) a factorisation of the embedding of the first-order semantic
--     domain into the higher-order one via a category of Grothendieck
--     Logical Relations (Fiore and Simpson 1999) (Theorem 5.1). See
--     the declaration "definability" in the conservativity module.
--
-- (2) every morphism definable in the higher-order language is
--     definable in the first-order language (Theorem 5.2). See the
--     declaration "syntactic-definability" in the conservativity
--     module.
import conservativity
