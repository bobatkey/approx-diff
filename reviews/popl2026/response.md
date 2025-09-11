We thank our three reviewers for their detailed reviews and suggestions for improving the paper. We address specific comments (C) and questions (Q) asked by each reviewer below, along with some proposed improvements to the paper.

# Responses to Reviewers

## Reviewer A

C1. _Some sections are highly technical and challenging for non-experts to follow._

C2. _Paper lacks empirical validation or comparisons with existing slicing tools_.

C3. _Paper does not address partiality or recursion_.

Q1. _Could the authors provide a high-level "roadmap" linking each theoretical component (e.g., Galois connection, CHAD) to its slicing/AD counterpart? This would improve accessibility._

Q2. _Is there any plan to implement this framework in a practical AD tool and compare slicing accuracy/performance with baseline methods?_

## Reviewer B

C1. _The title and abstract of the paper are misleading, as both refer to automatic differentiation._

C2. _I do not see how the contribution shows that Galois slicing is a "generalised form of automatic differentiation"_.

C3. _The paper does not discuss the existing literature on differential linear logic or probabilistic coherence spaces_.

Q1. _Do we have any counterexamples showing that $\mathrm{Fam}(\mathbf{LatGal})$ is not cartesian closed?_

Q2. _Could a more precise reference be given for Taylor's characterization of stability in terms of Galois connections?_

## Reviewer C

C1. _The evaluation could benefit from examples going beyond toy examples._

Q1. _Could the setting be extended into a source-to-source transformation?_

Q2. _Could the authors provide more end-to-end examples where such richer (quantitative) approximations yield insight unavailable in classical Galois slicing?_

Q3. _What is the computational overhead is of carrying slices alongside values?_

Q4. _How does the framework compare, qualitatively or quantitatively, with existing slicing/provenance techniques ?_

Q5. _Does the work on partiality and CHAD help in your setting?_


# List of Proposed Changes

