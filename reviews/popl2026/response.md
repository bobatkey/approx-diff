We thank our three reviewers for their detailed reviews and suggestions for improving the paper. We address specific comments (C) and questions (Q) asked by each reviewer below, along with some proposed improvements to the paper.

# Responses to Reviewers

## Reviewer A

C1. _Some sections are highly technical and challenging for non-experts to follow._

This is disappointing, and we hope that the addition of more examples in a future version will help to relieve some of the technical burden.

C2. _Paper lacks empirical validation or comparisons with existing slicing tools_.

This is true, and is something that we plan to address in future work.

C3. _Paper does not address partiality or recursion_.

This is true, and is something we plan to address in future work. Nevertheless, total programs do cover a large range of useful applications, such as database queries.

Q1. _Could the authors provide a high-level "roadmap" linking each theoretical component (e.g., Galois connection, CHAD) to its slicing/AD counterpart? This would improve accessibility._

We can certainly make the connections clearer in a future version, but for now:

- Galois connections are the counterpart of forward and reverse tangent maps of real smooth functions. The relationship of being a Galois connection replaces the fact that the forward and reverse maps are linear transposes of each other.

- CHAD is an approach to organising the implementation and semantics of AD. CHAD interprets a typed language with a real number type into the total category of some indexed category. The idea is that the indexing category represents the original functions, and the indexed category represents the tangent maps. Two interpretations are considered, one which is "syntactic" and so provides a source-to-source translation, and one which is "semantic" and interprets a term as a formal pairing of its functional meaning and its family of tangent maps. In our submission, we only do the semantic one but replace tangents with approximations and tangent maps with Galois connections. Because we formulated our results in Agda, the semantic variant is actually executable and was used for our examples, so we didn't prioritise a source-to-source version.

Q2. _Is there any plan to implement this framework in a practical AD tool and compare slicing accuracy/performance with baseline methods?_

We do not know if existing AD tools are appropriate as a basis for implementation, because they are specialised to real number differentiation, but we certainly plan to implement our ideas in a more practical tool to evaluate its performance. It may be possible to give a generic CHAD implementation that covers both.

## Reviewer B

C1. _The title and abstract of the paper are misleading, as both refer to automatic differentiation._

C2. _I do not see how the contribution shows that Galois slicing is a "generalised form of automatic differentiation"_.

We think that "misleading" is too harsh.

We think there are two parts to the reviewer's objection:

1. Is it correct that we appropriate "differentiation" and other words from real analysis in our setting? This is debatable, and certainly one could argue that absent any kind of definition of derivative as a limit that one should not use the word. Our argument is based on the similarity of structures (e.g., existence of tangent maps, meet preservation instead of linearity) outlined in Section 1.2, and on the conjectures about Tangent categories. The conjectures about Tangent categories (which in fact we have now proved for the forward case, the reverse case's definition is much more involved) extend the connection to the higher-order derivative case, but do not really say much more than that.

2. Whether or not this is a kind of automatic differentiation. Our argument here is based on the fact that we are proposing an interpretation of programs that computes forward and backwards maps of additional data at a point alongside the main computation. By the CHAD approach, this is exactly what first-order AD does, and so we think that the identification as a generalised form is valid.

C3. _The paper does not discuss the existing literature on differential linear logic or probabilistic coherence spaces_.

We admit that we should have done a more detailed survey of the literature on differential linear logic and how it relates to our setting. The connection between the trace and Taylor expansion may have something to say in our setting. A difference with DiLL is in the treatment of partiality and non-determinism. The Ehrhard survey referenced by the reviewer highlights these as key parts of DiLL, but, as we explained at the start of Section 3, we do not wish to admit either of these in our model for all functions -- they only apply to tangent maps. This was our motivation for moving from stable functions to the families construction.

Q1. _Do we have any counterexamples showing that $\mathrm{Fam}(\mathbf{LatGal})$ is not cartesian closed?_

We believe it is the case that $\mathrm{Fam}(\mathbf{LatGal})$ is not cartesian closed, but unfortunately we do not have a proof.

Q2. _Could a more precise reference be given for Taylor's characterization of stability in terms of Galois connections?_

FIXME

## Reviewer C

C1. _The evaluation could benefit from examples going beyond toy examples._

We agree, and plan to do this for future work.

Q1. _Could the setting be extended into a source-to-source transformation?_

Using the CHAD framework, we believe that this is very likely.

Q2. _Could the authors provide more end-to-end examples where such richer (quantitative) approximations yield insight unavailable in classical Galois slicing?_

We plan to do this in future work. The quantitative approximations came quite late in the development and we plan to explore it further.

Q3. _What is the computational overhead is of carrying slices alongside values?_

Probably quite high. If the semantics is compiled "as is", the slice transformations will be represented as closures closing over the computation so far. A source-to-source transformation, or a more intelligent representation of slice transformations could potentially avoid this.

Q4. _How does the framework compare, qualitatively or quantitatively, with existing slicing/provenance techniques ?_

We plan to do a detailed comparison in future work.

Q5. _Does the work on partiality and CHAD help in your setting?_

Most likely, yes.

# List of Proposed Changes

