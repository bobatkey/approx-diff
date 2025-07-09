{-# OPTIONS --prop --postfix-projections --safe #-}

module everything where

-- Examples from from section 1.1 of paper
import example

-- Proof from section 1.1 that CM (category of bounded meet semilattices and conditionally multiplicative
-- functions) is bicartesian closed
import bounded-meet

-- Proof from section 3 that Fam(C) is a cartesian closed if C has biproducts and all small products
-- (Lucatelli Nunes and Vákár 2023)
import families-exponentials

-- Proofs from Correctness of the Higher-Order Interpretation:
-- (1) a factorisation of the embedding of the first-order semantic domain into the higher-order one via a
--     category of Grothendieck Logical Relations (Hermida 1999)
-- (2) every morphism definable in the higher-order language is definable in the first-order language
import conservativity
