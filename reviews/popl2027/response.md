Thanks to the reviewers for their fair reviews. We are gratified that the reviewers think that the overall idea is worth pursuing, and their the connection between provenance and AD is novel and interesting. We agree that without a notion of "ground truth" of what kind of provenance we are addressing the current submission is difficult to assess. We have a plan for addressing this, which we outline below.

## Proposed Changes

For any final version of this submission, we propose to:

1. Add a discussion of first order data provenance (see below) that encompasses our examples and is lifted to higher order programs by the categorical constructions presented in the paper. This will address the points of Reviewers A and B. We will also summarise the connections between conjugate maps, pairs, and Galois connections as requested by Reviewer C.

2. Add some larger examples. We plan to add an example of a small expression language interpreter. Provenance tracking applied to an interpreter is a way to achieve program slicing, because it will reveal which parts of the input *program* contribute to the output.

3. Extend the discussion of related work, as requested by reviewer C.

The current version is only 23 pages long, so there is plenty of space for additional material.

## First-order Data Provenance [Reviewers A and B]

We have a model of first-order data provenance, which proceeds along similar lines to the logical relation approach suggested by Reviewer A:

1. We assume an ordered monoid R of "relatedness truth values" and a semiring "S" of "sensitivity values". The semiring S acts on the left on the monoid R via an operation $\rhd$.

2. A "base type" consists of a set $A$ with an $R$-valued binary relation $E$ of "relatedness".

3. An object consists of a sequence of base types $[(A_1, AE_1), ..., (A_n,AE_n)]$. This is roughly a "vector", but the notion of relatedness may be different at each dimension.

4. A morphism $f : [A_1, \dots, A_n] \to [B_1, \dots, B_m]$ is a pair of a function $f : A_1 \times \cdots \times A_n \to B_1 \times \cdots \times B_m$ and a function $\partial f$ from $A_1 \times \cdots \times A_n$ to $S$-valued $n$-by-$m$ matrices. These satisfy the condition that for all $x, x' \in \Pi_i A_i$ and $j$ with $0 \leq j < m-1$ we have $(\Sigma_i \partial f(x)_{i,j} \rhd AE_i(\pi_i x, \pi_i x')) \leq BE_j(f(x)_j,f(x')_j)$.

This construct gives a category with finite products that serves as a model of functions on tuples of first-order data with an intrinsic notion of derivative. The "Jacobian" associated with a function describes how each output position depends on the input positions collectively, at the given point. This can be seen as a "multi-category" version of metric space sensitivity, as studied in the context of differential privacy.

Specialising $R$ and $S$ to the booleans, with $x \rhd y = x \to y$ yields the boolean-valued examples in the paper, and similarly for the other examples.

## Connection to Lenses and Bidirectional Programming [Reviewer C]

We thank Reviewer C for the additional references. We have already cited the Cruttwell et al. 2024 paper at the top of page 12 (line 540) and noted that the $\mathrm{Fam}(C)$ construction we use is a generalisation of their lens based approach. Indeed, $\mathrm{Fam}(C)$ is sometimes called "dependent lenses" in other literature. We need the extra generality of dependency to make our category have sums and function spaces, where the "tangent space" varies according to the point.

We note that using lenses directly will not solve the problem of tying our derivatives to the functions. Indeed, in the Cruttwell et al. paper they inject Euclidean spaces and smooth functions into a category of lenses which forgets the connection. Lenses (and dependent lenses) treat functions and their derivatives of functions as a formal pairing. This seems to be essential to be able to lift the notion of derivative to higher order.

In a previous version of this paper, we conjectured that there is a connection between our work and Tangent Categories (Cockett and Cruttwell, Appl Categor Struct (2014) 22:331–417). Tangent Categories generalise the (Reverse) Derivative Categories approach to allow for tangent spaces that vary.

We were not aware of the two bidirectional transformation papers cited by Reviewer C, and will follow these up for any final version.
