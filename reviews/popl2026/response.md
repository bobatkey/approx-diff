We thank our three reviewers for their detailed reviews and suggestions for improving the paper. We address specific comments (C) and questions (Q) asked by each reviewer below.

# List of Proposed Changes

1. We will add more examples demonstrating how the Galois slicing works on larger programs. It is straightforward to add a datatype of arithmetic expressions to the language, where backwards slices of an interpreter for this language yield normal program slicing.

2. We will add more examples demonstrating the interval approximations and their relation to interval analysis.

3. We will add material further explaining the connection between our work and the CHAD presentation of Automatic Differentiation. See below for a short summary of the connection between CHAD, AD, and our work.

4. We will add a more in-depth discussion of DiLL and how it relates to our work.

# Responses to Reviewers

## Reviewer A

C1. _Some sections are highly technical and challenging for non-experts to follow._

This is disappointing, and we hope that the addition of more examples in a future version will help to relieve some of the technical burden.

C2. _Paper lacks empirical validation or comparisons with existing slicing tools_.

This is true, we will add more examples comparing to existing Galois slicing implementations, and comparison with other tools is something that we plan to address more deeply in future work.

C3. _Paper does not address partiality or recursion_.

This is true, and is something we plan to address in future work. Nevertheless, total programs do cover a large range of useful applications such as database queries constructed modularly with higher-order functions.

Q1. _Could the authors provide a high-level "roadmap" linking each theoretical component (e.g., Galois connection, CHAD) to its slicing/AD counterpart? This would improve accessibility._

We will make the connections clearer in a future version, but for now:

- Galois connections are the counterpart of forward and reverse tangent maps of real smooth functions. The relationship of being a Galois connection replaces the fact that the forward and reverse maps are linear transposes of each other.

- In relation to program slicing, the approximations ("tangents") in our approach are the slices of data values, and the Galois connections associated to a given execution of the program are the operations that push slices back and forth. The property that the back and forth operations form a Galois connection is the correctness property given by Perera et al.'s prior work.

- Unlike in normal differential geometry, we have no direct analogue of the real numbers. The approximation object in Section 3.3.3 is the closest, but does not account for the the interval approximation example in Section 3.3.4.

- CHAD is an approach to organising the implementation and semantics of AD. CHAD interprets a typed language with a real number type into the total category of some indexed category. The idea is that the indexing category represents the original functions, and the indexed category represents the tangent maps. In the CHAD work, two interpretations are considered, one which is "syntactic" and so provides a source-to-source translation, and one which is "semantic" and interprets a term as a formal pairing of its functional meaning and its family of tangent maps. The former is interpreted in the latter, and the latter is proved correct with respect to actual derivatives via a special purpose sconing argument similar to our Theorem 5.2. In our submission, we go directly to the semantic interpretation but replace tangents with approximations and tangent maps with Galois connections. Because we formulated our results in Agda, the semantic variant is actually executable and was used for our examples, so we didn't prioritise a source-to-source version. Moreover, we replace the specialised sconing / logical relations argument with a use of the Fiore and Simpson result, which is admittedly less elementary but highlights what is actually required for the correctness proof more clearly. Note that our approach also applies when $\mathrm{Fam}(\mathbf{LatGal})$ is replaced by $\mathbf{Man}$ and $\mathrm{Fam}(\mathbf{MeetSLat} \times \mathbf{JoinSLat}^{op})$ is replaced by $\mathrm{Fam}(\mathbf{Vect})$, recovering the original CHAD result with less work and at a higher level of abstraction.

Q2. _Is there any plan to implement this framework in a practical AD tool and compare slicing accuracy/performance with baseline methods?_

We do not know if existing AD tools are appropriate as a basis for implementation, because they are often specialised to real number differentiation, but we certainly plan to implement our ideas in a more practical tool than Agda to evaluate its performance. It may be possible to give a generic CHAD implementation that covers both.

## Reviewer B

C1. _The title and abstract of the paper are misleading, as both refer to automatic differentiation._

C2. _I do not see how the contribution shows that Galois slicing is a "generalised form of automatic differentiation"_.

We think that "misleading" is too harsh.

We think there are two parts to the reviewer's objection:

1. Is it correct that we appropriate "differentiation" and other words from real analysis in our setting? This is debatable, and certainly one could argue that absent any kind of definition of derivative as a limit, or use of linearity, that one should not use the word. Our argument is based on the similarity of structures (e.g., existence of tangent maps, meet preservation instead of linearity) outlined in Section 1.2, and on the conjectures about Tangent categories. The conjectures about Tangent categories (which in fact we have now proved for the forward case, the reverse case's definition is much more involved) extend the connection to the higher-order derivative case, but otherwise do not really say much more than that.

2. Whether or not this is a kind of automatic differentiation. Our argument here is based on the fact that we are proposing an interpretation of programs that computes forward and backwards maps of associated data along the main computation. Under the CHAD approach, this is exactly what first-order AD does, and so we think that the characterisation of our approach as a generalised form of AD valid.

C3. _The paper does not discuss the existing literature on differential linear logic or probabilistic coherence spaces_.

We admit that we should have done a more detailed survey of the literature on Differential Linear Logic and how it relates to our setting, especially given the common factor of Stability. A difference with DiLL is in the treatment of partiality and non-determinism. The Ehrhard survey referenced by the reviewer highlights these as key parts of DiLL, but, we do not wish to admit either of these in our model for all functions -- they only apply to tangent maps. This, as well the fact that approximations for us are not "real data", was part of our motivation for moving from stable functions to the families construction.

Q1. _Do we have any counterexamples showing that $\mathrm{Fam}(\mathbf{LatGal})$ is not cartesian closed?_

We believe it is the case that $\mathrm{Fam}(\mathbf{LatGal})$ is not cartesian closed, but unfortunately we do not have a proof.

Q2. _Could a more precise reference be given for Taylor's characterization of stability in terms of Galois connections?_

We don't have Taylor's book at hand to find the reference at the moment, but the results are part of Taylor's unpublished work on stable domain theory and its categorical generalisations at this url: https://www.paultaylor.eu/stable/ . Specifically, Theorem 1.11 in the manuscript "Quantitative Domains, Groupoids and Linear Logic" ( https://www.paultaylor.eu/stable/quadgl.pdf ).

## Reviewer C

C1. _The evaluation could benefit from examples going beyond toy examples._

We agree, and plan to do this for any future version.

Q1. _Could the setting be extended into a source-to-source transformation?_

Using the CHAD framework, we believe that this is very likely. The Vákár and Smeding paper already demonstrates this for real-number AD.

Q2. _Could the authors provide more end-to-end examples where such richer (quantitative) approximations yield insight unavailable in classical Galois slicing?_

The quantitative approximations came quite late in the development and we plan to explore the applications of it further.

Q3. _What is the computational overhead is of carrying slices alongside values?_

Probably quite high. If the semantics is compiled as a functional program, the slice transformations will be represented as closures closing over the computation so far.

A source-to-source transformation, or a more intelligent representation of slice transformations could potentially avoid this.

For example, if one was only interested in forward slicing with the approximation object in Section 3.3.3, one could represent this by a "dual numbers" approach similar to normal forward AD, where the approximation object is interpreted simply as a boolean (formally a pair of a unit (the point) and a boolean (the tangent), and the semantics then tracks this through the input.

Q4. _How does the framework compare, qualitatively or quantitatively, with existing slicing/provenance techniques ?_

We briefly mentioned some qualitative differences with existing slicing/provenance techniques in Section 6. We plan to do a detailed comparison in future work.

Q5. _Does the work on partiality and CHAD help in your setting?_

Most likely, yes, for languages with general recursion.
