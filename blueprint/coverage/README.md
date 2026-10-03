---
schema: autoform-coverage/v2
artifact: sources/hartshorne.md
artifact_sha256: e69438eeb09578513efca78c2298d4c91a2fa84d6d8c18aed026392dc003d9e5
---

# Coverage contract

What this project claims, and what it does not. The source is Robin Hartshorne,
*Algebraic Geometry*, Springer GTM 52, 1977; see the
[source notes](../sources/hartshorne.md) for locators.

This contract exhaustively partitions every LF-terminated line of the
project-authored source inventory. DECOMPOSED means that the inventory unit
has roadmap leaves; it does not mean that those leaves are proved.

| Unit | Area | Lines | Locator | Unit SHA-256 | Coverage | Evidence |
| --- | --- | --- | --- | --- | --- | --- |
| inventory-preamble | Bibliography and inventory policy | 1-18 | Source-notes preamble | 06a55218578c215cb988a903837572f9431c2ce7bd72305a6a86506357dad197 | OUT | Project-authored bibliographic metadata and roadmap policy, not a standalone mathematical target |
| chapter-i-section-1 | Affine varieties | 19-49 | Chapter I §1, book pp. 1–8 | ce343b2db86774cdb86b8efcd433d223715fe44c0d2be865fe6d99ae864a1bfa | DECOMPOSED | [The affine coordinate ring](../roadmap/affine-varieties/affine-coordinate-ring.md), [Affine space is a Noetherian space](../roadmap/affine-varieties/affine-space-noetherian.md), [Affine and quasi-affine varieties](../roadmap/affine-varieties/affine-variety.md), [Algebraic sets](../roadmap/affine-varieties/algebraic-set.md), [Every finitely generated domain is a coordinate ring](../roadmap/affine-varieties/coordinate-ring-realization.md), [The dimension of affine space](../roadmap/affine-varieties/dim-affine-space.md), [Dimension is the dimension of the coordinate ring](../roadmap/affine-varieties/dim-eq-coordinate-ring-dim.md), [A finitely generated algebra over a field has finite dimension](../roadmap/affine-varieties/dim-fg-algebra-finite.md), [Dimension of a finitely generated domain](../roadmap/affine-varieties/dim-fg-domain.md), [The dimension formula for a finitely generated domain](../roadmap/affine-varieties/dim-formula-catenary.md), [One inequality of the dimension formula](../roadmap/affine-varieties/dim-formula-inequality.md), [Dimension of a quasi-affine variety](../roadmap/affine-varieties/dim-quasi-affine.md), [Dimension of a topological space and of a ring](../roadmap/affine-varieties/dimension.md), [Krull dimension is invariant under integral extensions](../roadmap/affine-varieties/dimension-integral-extension.md), [Height is preserved by contraction along an integral extension](../roadmap/affine-varieties/height-comap-integral.md), [Hypersurfaces and codimension one](../roadmap/affine-varieties/hypersurface-dimension.md), [Decomposition into irreducible components](../roadmap/affine-varieties/irreducible-decomposition.md), [Hilbert's Nullstellensatz](../roadmap/affine-varieties/nullstellensatz.md), [A hypersurface in affine space drops the transcendence degree by one](../roadmap/affine-varieties/polynomial-hypersurface-trdeg.md), [Algebraic sets and radical ideals](../roadmap/affine-varieties/radical-ideal-correspondence.md), [A height-one prime drops the transcendence degree by one](../roadmap/affine-varieties/trdeg-drop-height-one.md), [The vanishing ideal](../roadmap/affine-varieties/vanishing-ideal.md), [The Zariski topology on affine space](../roadmap/affine-varieties/zariski-topology.md) |
| chapter-i-section-2 | Projective varieties | 50-77 | Chapter I §2, book pp. 8–14 | 7d1de7f5186c3c491bcde17d14773f8bfb013439247df789e36fa29fbe050ac9 | DECOMPOSED | [Varieties are covered by affine pieces](../roadmap/projective-varieties/affine-cover.md), [Dimension of the homogeneous coordinate ring](../roadmap/projective-varieties/homogeneous-coordinate-ring-dimension.md), [Homogeneous ideals](../roadmap/projective-varieties/homogeneous-ideal.md), [Algebraic sets and homogeneous radical ideals](../roadmap/projective-varieties/homogeneous-ideal-correspondence.md), [The homogeneous vanishing ideal](../roadmap/projective-varieties/homogeneous-vanishing-ideal.md), [Projective algebraic sets](../roadmap/projective-varieties/projective-algebraic-set.md), [Dimension in projective space](../roadmap/projective-varieties/projective-dimension.md), [The homogeneous Nullstellensatz](../roadmap/projective-varieties/projective-nullstellensatz.md), [Projective space](../roadmap/projective-varieties/projective-space.md), [Projective space is a Noetherian space](../roadmap/projective-varieties/projective-space-noetherian.md), [Projective and quasi-projective varieties](../roadmap/projective-varieties/projective-variety.md), [The Zariski topology on projective space](../roadmap/projective-varieties/projective-zariski-topology.md), [The standard affine charts](../roadmap/projective-varieties/standard-affine-charts.md), [Projective algebraic sets are finite unions of their components](../roadmap/intersections-projective-space/bezout/projective-components-finite-cover.md) |
| chapter-i-section-3 | Morphisms | 78-103 | Chapter I §3, book pp. 14–23, except Theorem 3.9A | f4da0c0a7240dbc99d6c481b930e8f40e9f55ed0caf8b3743f53724dec7e350d | DECOMPOSED | [Isomorphism via coordinate rings](../roadmap/morphisms/affine-iso-iff-algebra-iso.md), [Equivalence with finitely generated domains](../roadmap/morphisms/affine-variety-equivalence.md), [The local ring and function field of an affine variety](../roadmap/morphisms/affine-variety-rings.md), [The function field](../roadmap/morphisms/function-field.md), [The function field of an arbitrary variety](../roadmap/morphisms/function-field-abstract.md), [The function field is functorial for dominant morphisms](../roadmap/morphisms/function-field-functorial.md), [The underlying maps into germs and rational functions are injective](../roadmap/morphisms/function-field-injections.md), [The function field is the fraction field](../roadmap/morphisms/function-field-is-fraction-field.md), [The coordinate ring is the ring of regular functions](../roadmap/morphisms/global-regular-eq-coordinate-ring.md), [Global regular functions inside the function field](../roadmap/morphisms/global-functions/global-regular-in-function-field.md), [Global regular functions are the intersection of the local rings](../roadmap/morphisms/global-functions/global-regular-intersection-local-rings.md), [Morphisms into an affine variety](../roadmap/morphisms/hom-affine-bijection.md), [The local ring at a point](../roadmap/morphisms/local-ring.md), [The local ring is local](../roadmap/morphisms/local-ring-is-local.md), [The local ring is a localisation](../roadmap/morphisms/local-ring-is-localization.md), [Morphisms](../roadmap/morphisms/morphism.md), [Criterion for a morphism into an affine variety](../roadmap/morphisms/morphism-to-affine-criterion.md), [Points and maximal ideals](../roadmap/morphisms/points-eq-maximal-ideals.md), [The charts are isomorphisms of varieties](../roadmap/morphisms/projective-rings/chart-isomorphism.md), [Reading a global regular function on a chart](../roadmap/morphisms/projective-rings/chart-reading.md), [The degree bound](../roadmap/morphisms/projective-rings/degree-bound.md), [Graded localization](../roadmap/morphisms/projective-rings/graded-localization.md), [The homogeneous prime at a point](../roadmap/morphisms/projective-rings/point-ideal.md), [The function field of a projective variety](../roadmap/morphisms/projective-rings/projective-function-field.md), [The global regular functions of a projective variety](../roadmap/morphisms/projective-rings/projective-global-regular.md), [The local ring of a projective variety](../roadmap/morphisms/projective-rings/projective-local-ring.md), [An element stabilising a finite-dimensional subspace is integral](../roadmap/morphisms/projective-rings/stable-subspace.md), [Regular functions are continuous](../roadmap/morphisms/regular-function-continuous.md), [Regular functions on a quasi-affine variety](../roadmap/morphisms/regular-function-quasi-affine.md), [Regular functions on a quasi-projective variety](../roadmap/morphisms/regular-function-quasi-projective.md), [The ring of regular functions](../roadmap/morphisms/ring-of-regular-functions.md), [Varieties](../roadmap/morphisms/variety.md) |
| theorem-i-3-9a | Finiteness of integral closure | 104-112 | Chapter I, Theorem 3.9A, book p. 20 | dbf88fdad7ff0a3dea5bdf61a56cd1dd38bf8e971a521877c053ac68e1be014e | DECOMPOSED | [Frobenius is finite on an affine algebra over a perfect field](../roadmap/curve-normalization/frobenius-finite-affine-algebra.md), [Purely inseparable normalizations are finite](../roadmap/curve-normalization/purely-inseparable-normalization-finite.md), [Normalizations of polynomial rings are finite](../roadmap/curve-normalization/polynomial-normalization-finite.md), [Finiteness of integral closure](../roadmap/curve-normalization/finite-integral-closure.md) |
| exercise-i-3-3 | Local rings under morphisms | 113-125 | Chapter I, Exercise 3.3(a)–(c), book p. 21 | 16d93e4718933d93850ad380233e479301742d5f21cf936c7f1cd995aa21d5e6 | DECOMPOSED | [The local ring is functorial](../roadmap/morphisms/local-ring-functorial.md), [Isomorphisms from topology and local rings](../roadmap/projective-models/isomorphism-local-criterion.md), [Dense morphisms inject on local rings](../roadmap/projective-models/dominant-morphism-local-ring.md) |
| chapter-i-section-4 | Rational maps | 126-169 | Chapter I §4 running text and adopted prerequisites, book pp. 12, 13, 22, 24–29, 31 | 5e615fb1b35a06b273e6805caabd5d093a0f7569da356c7052f78485e1050ac1 | DECOMPOSED | [Open affine sets are a base for the topology](../roadmap/rational-maps/affine-base.md), [The birational criterion](../roadmap/rational-maps/birational-criterion.md), [Birational varieties have isomorphic open subsets](../roadmap/rational-maps/birational-open-subsets.md), [Birational varieties have isomorphic function fields](../roadmap/rational-maps/birational-function-fields.md), [Every variety is birational to a hypersurface](../roadmap/rational-maps/birational-hypersurface.md), [Birational maps](../roadmap/rational-maps/birational-map.md), [Blowing up a point](../roadmap/rational-maps/blowing-up.md), [The complement of a hypersurface is affine](../roadmap/rational-maps/hypersurface-complement.md), [The graph hypersurface has localized coordinate ring](../roadmap/rational-maps/principal-open-coordinate-ring.md), [Morphisms agreeing on an open set](../roadmap/rational-maps/morphism-agreement.md), [Products of varieties](../roadmap/rational-maps/product-variety.md), [The projective closure of an affine variety](../roadmap/rational-maps/projective-closure.md), [Composition of dominant rational maps](../roadmap/rational-maps/rational-map-composition.md), [Rational maps](../roadmap/rational-maps/rational-map.md), [Rational maps and function fields](../roadmap/rational-maps/rational-map-function-field.md), [The Segre embedding](../roadmap/rational-maps/segre-embedding.md), [Separably generated field extensions](../roadmap/rational-maps/separably-generated.md), [Quasi-projective curves have the cofinite topology](../roadmap/curve-normalization/quasiprojective-curve-cofinite.md) |
| chapter-i-section-5-geometry | Nonsingular varieties through Theorem 5.3 | 170-199 | Chapter I §5 from the opening definition through Theorem 5.3, book pp. 31–33 | ee362a68be872eca0b37655a6f2e2bea693cafb5441af3b14f55e0acdd17a6f1 | DECOMPOSED | [Regular local rings](../roadmap/nonsingular-varieties/regular-local-rings.md), [The cotangent-dimension bound](../roadmap/nonsingular-varieties/cotangent-dimension-bound.md), [Local rings are unchanged on open neighbourhoods](../roadmap/nonsingular-varieties/local-ring-open-invariance.md), [The cotangent space of affine space](../roadmap/nonsingular-varieties/ambient-cotangent-space.md), [The defining ideal and the local cotangent space](../roadmap/nonsingular-varieties/defining-ideal-cotangent-sequence.md), [Jacobian rank is independent of generators](../roadmap/nonsingular-varieties/jacobian-rank-invariance.md), [Nonsingular points of an affine variety](../roadmap/nonsingular-varieties/affine-nonsingular-points.md), [The Jacobian criterion](../roadmap/nonsingular-varieties/jacobian-criterion.md), [Intrinsic nonsingularity](../roadmap/nonsingular-varieties/intrinsic-nonsingularity.md), [The Jacobian rank bound](../roadmap/nonsingular-varieties/jacobian-rank-upper-bound.md), [Rank-drop loci are determinantal](../roadmap/nonsingular-varieties/determinantal-rank-locus.md), [The affine singular locus is closed](../roadmap/nonsingular-varieties/affine-singular-locus-closed.md), [Closedness from affine charts](../roadmap/nonsingular-varieties/singular-locus-closed.md), [An irreducible polynomial has a nonzero partial derivative](../roadmap/nonsingular-varieties/irreducible-polynomial-nonzero-partial.md), [An irreducible hypersurface has a nonsingular point](../roadmap/nonsingular-varieties/hypersurface-singular-locus-proper.md), [The singular locus is proper and closed](../roadmap/nonsingular-varieties/singular-locus.md) |
| chapter-i-section-5-completion | Completion and analytic local structure | 200-213 | Chapter I §5 after Theorem 5.3 through Examples 5.6.1–5.6.3, book pp. 33–35 | 16b6235edbcf411b8c62bddbc2c8662510e51d3c5d44c39fc756a20090eac7f2 | DEFERRED | Deferred pending a separately approved completion/Cohen milestone; these results are not needed for Theorems 5.1–5.3 |
| chapter-i-section-5-exercises | Elimination theory and §5 exercises | 214-224 | Chapter I Theorem 5.7A and Exercises 5.1–5.15, book pp. 35–39 | 2ac2976a7885e32ef668d86998813d14e82fe99f82efaa465490912eb3bc8e3e | OUT | Theorem 5.7A is introduced only for Exercise 5.15, and no §5 exercise is adopted by the approved main-text scope |
| chapter-i-section-6-valuations | Valuation rings, DVRs, and Dedekind localizations | 225-242 | Chapter I §6 through Theorem 6.2A and the following Dedekind observation, book pp. 39–40 | f31487b6d972e64e19d2522573f81dd8a88195b3bc9c3dcdec4720b2862fb11a | DECOMPOSED | [Curves](../roadmap/nonsingular-curves/curve.md), [Valuation rings are maximal local subrings](../roadmap/nonsingular-curves/valuation-ring-maximal-local-subring.md), [Every local subring is dominated by a valuation ring](../roadmap/nonsingular-curves/valuation-ring-dominates-local-subring.md), [Characterizations of discrete valuation rings](../roadmap/nonsingular-curves/dvr-characterizations.md), [Localizations of a Dedekind domain are DVRs](../roadmap/nonsingular-curves/dedekind-localization-dvr.md) |
| theorem-i-6-3a | Integral closure of a Dedekind domain | 243-256 | Chapter I, Theorem 6.3A, book p. 40 | feba44cd6545ac51939eb3b64dc66a51be1e9d6e0a6b3cb1bbb3978628bbdc36 | DECOMPOSED | [Principal quotient length](../roadmap/curve-normalization/krull-akizuki/krull-akizuki-principal-quotient-length.md), [finite-length ideal quotients](../roadmap/curve-normalization/krull-akizuki/krull-akizuki-quotient-finite.md), [Krull–Akizuki](../roadmap/curve-normalization/krull-akizuki/krull-akizuki.md), [integral closures of Dedekind domains](../roadmap/curve-normalization/krull-akizuki/dedekind-integral-closure.md) |
| chapter-i-section-6-local-structure | Local structure of nonsingular curves and point separation | 257-272 | Chapter I §6 after Theorem 6.3A through Lemma 6.4, book p. 41 | 449002e69a8a7a1a3cba7af6c3431990167071a14df73facf7f8b0a3fedfc2e3 | DECOMPOSED | [Curves](../roadmap/nonsingular-curves/curve.md), [The function field is the fraction field of every local ring](../roadmap/nonsingular-curves/local-ring-fraction-field.md), [Dimension of the local ring of a variety](../roadmap/nonsingular-curves/local-ring-dimension.md), [Local rings of nonsingular curves are DVRs](../roadmap/nonsingular-curves/nonsingular-curve-local-ring-dvr.md), [Nonsingular curve points define discrete valuations](../roadmap/nonsingular-curves/nonsingular-curve-valuation.md), [Linear fractions separate projective points](../roadmap/nonsingular-curves/projective-linear-separation.md), [Membership of a homogeneous fraction in a local ring](../roadmap/nonsingular-curves/homogeneous-fraction-local-membership.md), [The local ring determines the point](../roadmap/nonsingular-curves/local-ring-inclusion-determines-point.md) |
| chapter-i-section-6-normalization | Normalization, finite poles, and affine DVR models | 273-291 | Chapter I §6, Lemma 6.5 and Corollary 6.6, book pp. 41–42 | fa8a7c43b84a8bc9188df4ff8485d455c3047445f73e7e3c9ee4dfecee6645b2 | DECOMPOSED | [Discrete valuation rings of a function field](../roadmap/curve-normalization/function-field-dvrs.md), [One-dimensional function fields have separating parameters](../roadmap/curve-normalization/separating-parameter.md), [The two separable normalization charts](../roadmap/curve-normalization/separable-normalization-charts.md), [A DVR containing a Dedekind subring is its localization](../roadmap/curve-normalization/dedekind-subring-localization.md), [Dedekind localizations occur on nonsingular affine curves](../roadmap/curve-normalization/dedekind-affine-model.md), [A rational function has finitely many poles](../roadmap/curve-normalization/finite-poles.md), [Every function-field DVR has a nonsingular affine model](../roadmap/curve-normalization/dvr-affine-model.md) |
| chapter-i-section-6-abstract-curves | Valuation-space and abstract nonsingular curves | 292-315 | Chapter I §6, definitions and Proposition 6.7, book pp. 42–43 | 364f65bc543535d335016e2307173f2b5ad811d68b01251e81d6d3318182621c | DECOMPOSED | [Quasi-projective curves have the cofinite topology](../roadmap/curve-normalization/quasiprojective-curve-cofinite.md), [The cofinite valuation space](../roadmap/curve-normalization/valuation-space/valuation-space-topology.md), [The valuation space is infinite](../roadmap/curve-normalization/valuation-space/valuation-space-infinitude.md), [Residue fields of function-field DVRs](../roadmap/curve-normalization/valuation-residue-field.md), [Regular functions on the valuation space](../roadmap/curve-normalization/valuation-regular-functions.md), [The valuation-space regularity axioms](../roadmap/curve-normalization/valuation-regular-functions-local.md), [Abstract nonsingular curves](../roadmap/curve-normalization/abstract-nonsingular-curve.md), [The function field of an abstract nonsingular curve](../roadmap/curve-normalization/valuation-space-function-field.md), [Nonsingular affine curves have Dedekind coordinate rings](../roadmap/curve-normalization/nonsingular-affine-curve-dedekind.md), [The local-ring map has open image](../roadmap/curve-normalization/curve-local-ring-map-open.md), [Nonsingular curves are open subcurves of their valuation spaces](../roadmap/curve-normalization/curve-to-valuation-space-iso.md) |
| chapter-i-section-6-projective-model | Extension across points and projective models | 316-340 | Chapter I §6, Proposition 6.8 through Corollary 6.12, book pp. 43–46 | 7298a810773cda8b7a437aaede7938bbfd6699045a27a79973977529c89fbece | DECOMPOSED | [Regularity near a valuation](../roadmap/projective-models/regular-near-valuation.md), [The local ring of an abstract curve](../roadmap/projective-models/abstract-curve-local-ring.md), [Abstract valuation curves have dimension one](../roadmap/projective-models/abstract-curve-dimension.md), [Transporting valuation curves along a field equivalence](../roadmap/projective-models/valuation-space-field-equivalence.md), [A projective coordinate pivot](../roadmap/projective-models/valuation-projective-pivot.md), [Extension to a projective target](../roadmap/projective-models/projective-extension.md), [A two-chart affine cover](../roadmap/projective-models/two-affine-chart-cover.md), [Projective chart extensions](../roadmap/projective-models/projective-chart-extensions.md), [The projective diagonal model](../roadmap/projective-models/projective-diagonal.md), [Its function field](../roadmap/projective-models/projective-model-function-field.md), [Its local rings](../roadmap/projective-models/projective-model-local-rings.md), [A dominating function-field DVR](../roadmap/projective-models/dominating-dvr.md), [Nonsingular projective models of function fields](../roadmap/projective-models/function-field-projective-model.md), [Abstract curves are quasi-projective](../roadmap/projective-models/abstract-curve-quasiprojective.md), [Completion of a nonsingular curve](../roadmap/projective-models/nonsingular-curve-projective-open.md), [Projective models of curves](../roadmap/projective-models/curve-projective-model.md), [The three curve categories](../roadmap/projective-models/curve-categories.md), [Extension of dominant rational maps](../roadmap/projective-models/projective-rational-map-extension.md), [Projective and quasi-projective curve categories](../roadmap/projective-models/projective-quasiprojective-curve-equivalence.md), [Quasi-projective curves and function fields](../roadmap/projective-models/quasiprojective-curve-function-field-equivalence.md), [The curve/function-field category equivalence](../roadmap/projective-models/curve-category-equivalence.md) |
| chapter-i-section-6-exercises | Exercises on curves and valuations | 341-346 | Chapter I, Exercises 6.1–6.7, book pp. 46–47 | 75ef55d17275e74c30a42767df0d4e799460fd6de6f993da682490c70135379b | OUT | No §6 exercise is used by the approved scope through Corollary 6.12 |
| remaining-book-inventory-policy | Coarse-pass and exercise policy | 347-360 | Remaining-book inventory policy | 6199596f63af95e632ecbc18b74b121b339d3b79ae1d97b3abb8d9092b380e92 | OUT | Project-authored inventory policy rather than a mathematical target |
| chapter-i-section-7-main | Intersections, Hilbert polynomials, degree, and Bézout | 361-396 | Chapter I §7 running text through Remark 7.8.2 and required earlier exercises, book pp. 12, 22, 47–54 | 52908f71b19418242bef909a04ebdc4dd9ad670c6bed49ef414495a244a4f82e | DECOMPOSED | [Affine components as minimal primes of a cut ideal](../roadmap/intersections-projective-space/dimension/affine-components-minimal-primes.md), [Dimension of the affine cone](../roadmap/intersections-projective-space/dimension/affine-cone-dimension.md), [The affine cone and its ideal](../roadmap/intersections-projective-space/dimension/affine-cone-ideal.md), [Irreducibility of the affine cone](../roadmap/intersections-projective-space/dimension/affine-cone-irreducible.md), [The diagonal section of an affine product](../roadmap/intersections-projective-space/dimension/affine-diagonal-section.md), [The affine dimension theorem](../roadmap/intersections-projective-space/dimension/affine-dimension-theorem.md), [The coordinate ring of an affine product](../roadmap/intersections-projective-space/dimension/affine-product-coordinate-ring.md), [Dimension of an affine product](../roadmap/intersections-projective-space/dimension/affine-product-dimension.md), [Affine products are varieties](../roadmap/intersections-projective-space/dimension/affine-product-variety.md), [Degree is additive across a top-dimensional union](../roadmap/intersections-projective-space/bezout/degree-union.md), [A finite set of equations lowers component dimension by at most its size](../roadmap/intersections-projective-space/dimension/finite-cut-component-dimension.md), [Finite-dimensional graded pieces](../roadmap/intersections-projective-space/hilbert/finite-graded-pieces.md), [Homogeneous annihilators and cyclic modules](../roadmap/intersections-projective-space/hilbert/graded-annihilator.md), [Integer-graded module twists](../roadmap/intersections-projective-space/hilbert/graded-module-twists.md), [Multiplicity in a graded prime filtration](../roadmap/intersections-projective-space/hilbert/graded-multiplicity.md), [Graded prime filtrations](../roadmap/intersections-projective-space/hilbert/graded-prime-filtration.md), [Integer-graded submodules and quotients](../roadmap/intersections-projective-space/hilbert/graded-submodules-and-quotients.md), [The Hilbert function](../roadmap/intersections-projective-space/hilbert/hilbert-function.md), [A nonempty projective algebraic set has positive integral degree](../roadmap/intersections-projective-space/bezout/hilbert-polynomial-positive-degree.md), [Hilbert polynomials of shifted prime quotients](../roadmap/intersections-projective-space/hilbert/hilbert-polynomial-prime-quotient.md), [Hilbert–Serre](../roadmap/intersections-projective-space/hilbert/hilbert-serre.md), [A degree-d hypersurface has degree d](../roadmap/intersections-projective-space/bezout/hypersurface-hilbert-polynomial.md), [The hypersurface-section coordinate-ring sequence is exact](../roadmap/intersections-projective-space/bezout/hypersurface-section-exact-sequence.md), [The Hilbert polynomial of a hypersurface section is a difference](../roadmap/intersections-projective-space/bezout/hypersurface-section-hilbert-polynomial.md), [The integer grading on a polynomial ring](../roadmap/intersections-projective-space/hilbert/integer-polynomial-grading.md), [Discrete antidifferentiation of a numerical polynomial](../roadmap/intersections-projective-space/hilbert/numerical-antidifference.md), [Numerical polynomials have integral binomial expansions](../roadmap/intersections-projective-space/hilbert/numerical-binomial-expansion.md), [Numerical polynomials](../roadmap/intersections-projective-space/hilbert/numerical-polynomial.md), [Bézout's theorem for distinct plane curves](../roadmap/intersections-projective-space/bezout/plane-curve-bezout.md), [Minimal primes in a graded prime filtration](../roadmap/intersections-projective-space/hilbert/prime-filtration-support.md), [Projective codimension one is a hypersurface](../roadmap/intersections-projective-space/dimension/projective-codimension-one-hypersurface.md), [Proper closed subsets of projective varieties have smaller dimension](../roadmap/intersections-projective-space/dimension/projective-proper-closed-dimension-drop.md), [The projective dimension theorem for components](../roadmap/intersections-projective-space/dimension/projective-dimension-theorem.md), [Hilbert polynomials and degrees of projective algebraic sets](../roadmap/intersections-projective-space/hilbert/projective-hilbert-polynomial-and-degree.md), [Projective intersection components correspond to minimal primes](../roadmap/intersections-projective-space/bezout/projective-intersection-components-minimal-primes.md), [Proper hypersurface sections are equidimensional](../roadmap/intersections-projective-space/bezout/hypersurface-section-components-equidimensional.md), [Bézout for a projective variety and a hypersurface](../roadmap/intersections-projective-space/bezout/projective-hypersurface-bezout.md), [Projective intersection components on an affine chart](../roadmap/intersections-projective-space/dimension/projective-intersection-components.md), [Intersection multiplicity with a hypersurface](../roadmap/intersections-projective-space/bezout/projective-intersection-multiplicity.md), [Projective varieties of complementary dimension meet](../roadmap/intersections-projective-space/dimension/projective-intersection-nonempty.md), [A zero-dimensional projective variety is a point](../roadmap/intersections-projective-space/bezout/projective-zero-dimensional-variety-point.md), [A projective point has Hilbert polynomial and degree one](../roadmap/intersections-projective-space/bezout/projective-point-degree.md), [Projective space has degree one](../roadmap/intersections-projective-space/bezout/projective-space-hilbert-polynomial.md), [Projective algebraic sets are finite unions of their components](../roadmap/intersections-projective-space/bezout/projective-components-finite-cover.md), [Degree of a pure projective curve is the sum of component degrees](../roadmap/intersections-projective-space/bezout/pure-projective-curve-degree-components.md), [Pointwise multiplicity for reducible plane curves](../roadmap/intersections-projective-space/bezout/reducible-plane-curve-pointwise-multiplicity.md), [Bézout for reducible plane curves without a common component](../roadmap/intersections-projective-space/bezout/reducible-plane-curve-bezout.md), [Dimension of a tensor product of affine domains](../roadmap/intersections-projective-space/dimension/tensor-product-dimension.md), [The leading Hilbert coefficient is a sum over minimal primes](../roadmap/intersections-projective-space/bezout/top-dimensional-prime-filtration-leading-term.md), [The coordinate-ring sequence for a union is exact](../roadmap/intersections-projective-space/bezout/union-coordinate-ring-exact-sequence.md) |
| chapter-i-section-7-local-comparison | Comparison with local plane-curve intersection multiplicity | 397-404 | Chapter I, Remark 7.8.1, book p. 54, referring to Exercise 5.4 on p. 36 | e2de19386bae45b3cc837a8a31b528b1177158d4e49e67065150aeff3f8895e4 | DEFERRED | Deferred to an explicit local intersection-multiplicity milestone because Hartshorne supplies neither the proof nor an adopted proof source |
| chapter-i-section-7-classical-degree-exercises | Generic-line interpretation and unadopted §7 exercises | 405-413 | Chapter I, Exercises 5.4 and 7.1–7.8, book pp. 36, 54–55 | fdddcd78038ff2e067c585adf28aa3585a606104194a55918785f418c27ea2cd | OUT | Exercise 7.4's generic-line interpretation depends on unadopted Exercises 7.3 and 5.4, and no later adopted running-text proof uses this exercise chain |
| chapter-i-section-8-recaps | Chapter I recaps in the closing survey | 414-416 | Chapter I §8, book pp. 55–59 | d921d39f4fe999ba4ea1648370ef24cf5f317540b743e5d781cdaff765fc55be | DECOMPOSED | [Rational maps and function fields](../roadmap/rational-maps/rational-map-function-field.md), [the birational criterion](../roadmap/rational-maps/birational-criterion.md), [completion of a nonsingular curve](../roadmap/projective-models/nonsingular-curve-projective-open.md), [the curve/function-field category equivalence](../roadmap/projective-models/curve-category-equivalence.md), [open affine sets form a base](../roadmap/rational-maps/affine-base.md), and [affine varieties correspond to finitely generated domains](../roadmap/morphisms/affine-variety-equivalence.md) |
| chapter-i-section-8-later-previews | Later-chapter mathematical previews | 417-420 | Chapter I §8, book pp. 56–59 | 110b05c0b422ba592088d5efd25e838251f8f4c420a6cd334d3a58a2d8febc02 | DEFERRED | Delegated to the approved [Chapter II](../roadmap/remaining-book/README.md#chapter-ii-schemes), [Chapter III](../roadmap/remaining-book/README.md#chapter-iii-cohomology), [Chapter IV](../roadmap/remaining-book/README.md#chapter-iv-curves), [Chapter V](../roadmap/remaining-book/README.md#chapter-v-surfaces), and [Appendix](../roadmap/remaining-book/README.md#appendices) milestones, where the survey claims receive precise hypotheses and sources |
| chapter-i-section-8-standalone | Standalone survey source obligations | 421-421 | Chapter I §8, book pp. 56–59 | dde93cbfd06ab4216cb2ec360a214ed0b45cffe2a1b4610b20cffcd047039004 | DEFERRED | [Section I.8 disposition](../roadmap/remaining-book/README.md#section-i8-disposition): precise moduli, embedding-dependence, and infinite-dimensional Noetherian-spectrum statements await adopted proof sources |
| chapter-i-section-8-exposition | Philosophical, historical, and motivational survey prose | 422-423 | Chapter I §8, book pp. 55–59 | 6162c04319dab3f3b16242bfa088940c32a5591e11a09149df8f8b445fc9225f | OUT | Editorial framing, historical notes, Fermat motivation, cautions about generality, and chapter navigation are not mathematical formalization targets |
| chapter-ii | Schemes | 424-443 | Chapter II, book pp. 60–200 | 5ab3025214dd544fe50ee9d154af607e1df78091a824264b15748826c7c543f7 | DEFERRED | [Approved Chapter II milestones](../roadmap/remaining-book/README.md#chapter-ii-schemes), sequenced after the active §I.7 milestone and exact Mathlib matching |
| chapter-iii | Cohomology | 444-458 | Chapter III, book pp. 201–292 | 0b23d7aabb70babbbdf4b92455c994740b40c84e4234ff0a99a05e960c4170b3 | DEFERRED | [Approved Chapter III milestones](../roadmap/remaining-book/README.md#chapter-iii-cohomology), sequenced after Chapter II and adoption of proof sources for quoted background |
| chapter-iv | Curves | 459-473 | Chapter IV, book pp. 293–355 | 0aff55cb2f727f4b9f6a310b417e684c5654ecf92ff49d5ea80a1d1ff2adaa9f | DEFERRED | [Approved Chapter IV milestones](../roadmap/remaining-book/README.md#chapter-iv-curves), sequenced after Chapters II–III and adoption of analytic sources |
| chapter-v | Surfaces | 474-489 | Chapter V, book pp. 356–423 | a67588f1b952c580330c84bd57bcbe2beb59abab5a9e184d307b3490a3176e81 | DEFERRED | [Approved Chapter V milestones](../roadmap/remaining-book/README.md#chapter-v-surfaces), sequenced after Chapters II–IV with survey claims separately sourced |
| appendix-a | Intersection theory | 490-505 | Appendix A, book pp. 424–437 | c272e216776da6794c43a4b564e7a43327f8b45e51161877d1b547d36789d1fb | DEFERRED | [Approved Appendix A milestones](../roadmap/remaining-book/README.md#appendices), sequenced after the prerequisite scheme, cohomology, curve, and surface milestones |
| appendix-b | Transcendental methods | 506-520 | Appendix B, book pp. 438–448 | f81e1ac1d11e7d0d86bd85caedc5a2e1877ab4fea72a4313604db713ff4f6650 | DEFERRED | [Approved Appendix B milestones](../roadmap/remaining-book/README.md#appendices), pending the recorded analytic and Hodge-theoretic source stack |
| appendix-c | The Weil conjectures | 521-536 | Appendix C, book pp. 449–458 | 070ba0efbef266000c770f47cb1b551306790ebf7a29338f75c3e80a646b27ef | DEFERRED | [Approved Appendix C milestones](../roadmap/remaining-book/README.md#appendices), pending the recorded étale and ℓ-adic source stack |
| back-matter | Bibliography and reference apparatus | 537-544 | Book pp. 459 onward | 1b1fd5ef5548c11d97cd83fd41557f43b4a51874da0e4edb83b9f4366f1df20c | OUT | Bibliography, algebra-reference list, glossary, and index rather than new theorem targets |
| standing-conventions | Algebraically closed base field and irreducible varieties | 545-552 | Standing conventions for Chapter I | 32c55ea4bf211d1ee39edc51f124ebc7e3841b0728a82001ac113c4cff8be7df | DECOMPOSED | [Affine and quasi-affine varieties](../roadmap/affine-varieties/affine-variety.md), [Projective and quasi-projective varieties](../roadmap/projective-varieties/projective-variety.md), [Varieties](../roadmap/morphisms/variety.md) |

## Approved fine scope

Chapter I, sections 1 through 4 (book pages 1–29), the geometric core of
section 5 through Theorem 5.3 (book pages 31–33), and section 6 through
Corollary 6.12 (book pages 39–46), including the quoted Theorems 3.9A and
6.3A and Exercise 3.3(a)–(c), which Hartshorne uses in Theorem 6.9. The active
fine scope also includes §I.7's running text through Remark 7.8.2 and the
earlier exercises required by its proofs:

| Section | Title | Pages | Articles | State |
| --- | --- | --- | --- | --- |
| I.1 | Affine Varieties | 1–8 | [23 articles](../roadmap/affine-varieties/README.md) | done |
| I.2 | Projective Varieties | 8–14 | [13 articles](../roadmap/projective-varieties/README.md) | done |
| I.3 | Morphisms | 14–23 | [33 articles](../roadmap/morphisms/README.md) | done |
| I.3, Ex. 3.3(b),(c) | Local-ring criteria used by Thm. 6.9 | 21 | [Dense morphisms inject on local rings](../roadmap/projective-models/dominant-morphism-local-ring.md), [isomorphisms from topology and local rings](../roadmap/projective-models/isomorphism-local-criterion.md) | done |
| I.4 | Rational Maps | 24–29 | [17 articles](../roadmap/rational-maps/README.md) | done |
| I.4, Ex. 4.8(a) consequence | Infinitude used in §6 | 31 | [1 article](../roadmap/curve-normalization/quasiprojective-curve-cofinite.md) | done |
| I.5 through Thm. 5.3 | Nonsingular Varieties | 31–33 | [16 articles](../roadmap/nonsingular-varieties/README.md) | done |
| I.6 through Lem. 6.4, excluding Thm. 6.3A | Local Structure of Nonsingular Curves | 39–41 | [12 articles](../roadmap/nonsingular-curves/README.md) | done |
| I.3.9A and I.6.3A–6.7 | Normalization and the Valuation-Space Curve | 20, 40–43 | [26 articles](../roadmap/curve-normalization/README.md) | done |
| I.6.8–6.12 | Projective Models and Curve Categories | 43–46 | [21 further articles in the 23-leaf chapter](../roadmap/projective-models/README.md) | done |
| I.7 main text and required prerequisites | Intersections, Hilbert Polynomials, Degree, and Bézout | 12, 22, 47–54 | [50 articles](../roadmap/intersections-projective-space/README.md) | 47 done, 3 planned |

All 86 main-text and previously adopted articles in §§1–4 are done: 85 are
proved here and one was already in Mathlib. The §4 results include the
rational-map core through Corollary 4.5,
separability, projective closure, the Segre/product construction, the
hypersurface normal form, and blowing up. The approved part of §5 adds 16
articles: Mathlib supplies the exact regular-local/cotangent criterion, and the
other 15 are proved here. Thus all 102 scoped targets are complete: 100 are
proved in this project and two are supplied by Mathlib.

Exercise 3.3(a) is already among those completed articles under its corrected
source provenance. Parts (b) and (c), newly adopted because Theorem 6.9 uses
them, are the first two formalized leaves of the 23-leaf projective-model
milestone.

The approved opening of §6 adds 12 targets. Mathlib supplies the two clauses of
Theorem 6.1A exactly, and the other ten are proved in this project. That
114-leaf roadmap is complete: 110 project formalizations and four Mathlib
results.

The normalization and valuation-space milestone adds 26 leaves: eight
for the exact nonseparable background theorems, seven for finite poles and
affine DVR models, and eleven for abstract nonsingular curves through
Proposition 6.7. All 26 are formalized. The enlarged roadmap has 140 leaves,
all complete: 136 project formalizations and four exact Mathlib results.
The geometric branch uses two separable normalization charts, so it can advance
independently of the harder exact Theorems 3.9A and 6.3A.

The projective-model milestone adds 23 leaves: the two Exercise 3.3 criteria
and 21 leaves for Proposition 6.8 through Corollary 6.12. All 23 are now
formalized. The completed preceding roadmap therefore has 163 leaves: 159
proved in this project and four supplied by Mathlib. The §I.7 fine roadmap has
50 leaves: 47 formalized and three remaining, for 213 formalizable leaves in
the current graph.

The counts grow as the work goes on, almost always by splitting a node that
turned out to hold more than one pull request's worth of Lean; where the scope
itself widened, as it did for §4, this contract says so. The result-to-article
map in the source notes is the record of which numbered results ended up
where.

Every result the main text of those scoped spans proves or uses is covered by
an article. Some articles carry more than one numbered result when they land
together: Propositions 1.5 and 1.6 share one, and Theorem 1.11A, Proposition
1.12A and Proposition 1.13 share another. The
[source notes](../sources/hartshorne.md) give the result-to-article map.

Some exercises are covered too, under one rule: **an exercise is adopted when
the main text of an in-scope section depends on it.** Nothing else is adopted.

- **Exercises 2.1–2.7**, because Hartshorne states the projective
  Nullstellensatz, the homogeneous ideal correspondence, and both projective
  dimension computations as exercises and then relies on them in §3.
- **Exercise 2.9**, the projective closure of an affine variety, because
  Proposition 4.9 ends by taking one.
- **Exercises 2.14 and 3.16**, the Segre embedding and products of
  quasi-projective varieties, because the blowing-up construction of §4 lives in
  `𝔸ⁿ × ℙⁿ⁻¹`. Only parts (a) and (b) of 3.16 are claimed, together with the
  two clauses of the starred part (c) that §4 consumes: the projections are
  morphisms and a pair of morphisms into the factors induces one into the
  product.
- **Exercise 4.8(a)** only in the weak form needed before Proposition 6.7:
  a positive-dimensional quasi-projective variety has infinitely many points.
  Its exact cardinality statement and part (b) remain outside the roadmap.
- **Exercise 3.3(a)–(c)** because Theorem 6.9 explicitly uses functorial local
  rings, injectivity for a dense morphism, and the isomorphism criterion from a
  homeomorphism with isomorphic local rings. All three parts are formalized.

**The two quoted integral-closure results are formalized.** Theorem 3.9A
(finiteness of integral closure, p. 20) and Theorem 6.3A enter with Lemma 6.5.
The closest pinned-Mathlib declarations assume separability, while Hartshorne's
statements do not, so the roadmap includes explicit nonseparable branches.

The first target was Corollary I.3.8, the arrow-reversing equivalence between
affine varieties over `k` and finitely generated integral domains over `k`.
Theorem 4.4 is its birational counterpart: varieties with dominant rational
maps are equivalent, arrows reversed, to finitely generated field extensions of
`k`. The declared §4 scope continues through Proposition 4.9 and the blow-up
construction on pages 28–29. The §5 milestone develops the Jacobian criterion
and ends with Theorem 5.3, that the singular locus is a proper closed subset;
that milestone is complete. The §6 milestone identifies the local rings of
nonsingular curves as DVRs and proves Lemma 6.4, that inclusion of local rings
inside the function field determines the point; it is complete as well. The
completed normalization milestone proves finite poles, realizes every
function-field DVR on a nonsingular affine curve, constructs the
valuation-space regular-function structure, and ends with Proposition 6.7.
The completed projective-model milestone extends morphisms over missing points,
constructs nonsingular projective models, and ends with the equivalences of
Corollary 6.12.

## Deferred and out of scope

**The rest of §5 after Theorem 5.3.** Completion, Theorems 5.4A and 5.5A, and
analytic isomorphism through Examples 5.6.1–5.6.3 are deferred to a separately
approved completion milestone. Theorem 5.7A is out of scope because it is
introduced only for Exercise 5.15.

**The exercises of Chapter I §6.** Proposition 6.8 through Corollary 6.12 are
now decomposed; the §6 exercises remain out of scope.

**The later mathematical body.** Section I.8, Chapters II–V, and Appendices
A–C have an [approved coarse milestone map](../roadmap/remaining-book/README.md)
and are explicitly deferred while §I.7 is active. Their section boundaries and
broad dependency spine have been checked, but they carry no formalizable leaves
yet. Appendix C's historical material and the bibliography/reference apparatus
will not generate theorem targets merely because they occur in the source.

**The exercises of §§4–5, and every exercise not listed above.** Hartshorne has
more than four hundred exercises. The ones adopted are adopted because the main
text depends on them, and that is the only criterion applied. Exercise 3.16(c)
is adopted only in the weak form stated above, not as the full categorical
product.

**Results Hartshorne quotes without proof.** Statements he numbers with a
trailing `A` are commutative algebra imported from Atiyah–Macdonald, Matsumura
and Zariski–Samuel. They carry `origin: background` and are prerequisites rather
than claims against the source. Where the pinned Mathlib already proves one, the
article records the upstream declaration and the work is to check that the
statement matches. Checked against the pinned checkout:

- **I.1.3A**, Hilbert's Nullstellensatz, is
  `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`, under
  `[IsAlgClosed K] [Finite σ]`. Hartshorne's case is the specialisation `K = k`.
  This is one of four articles in the expanded project asserting
  `mathlib: true`.
- **I.1.12A** is
  `UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one`, an exact
  match for "a Noetherian domain is a UFD iff every height-one prime is
  principal".
- **I.1.11A**, Krull's Hauptidealsatz, is matched in two pieces:
  `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes` gives `p.height ≤ 1`
  for a prime minimal over a principal ideal, and
  `Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors` gives the reverse
  under Hartshorne's non-zero-divisor hypothesis. The packaged
  `Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors` is the ideal-level
  form and is what Exercise 2.6 uses.

**I.1.8A**, that a finitely generated `k`-algebra domain has Krull dimension
equal to the transcendence degree of its fraction field, and that
`height 𝔭 + dim B/𝔭 = dim B`, is **not** in the pinned Mathlib in either form.
It was the chapter's largest single piece of background work and is now proved
here: part (a) through Noether normalisation, part (b) by induction on the
height with the height-one case going through a Noether normalisation of its
own.

**I.5's regular-local definition** has an exact pinned-Mathlib formulation:
`IsRegularLocalRing.iff_finrank_cotangentSpace` identifies Mathlib's
`IsRegularLocalRing` class with Hartshorne's equality
`dim_κ 𝔪/𝔪² = dim A`. Proposition 5.2A is not a single upstream declaration;
its project wrapper combines `ringKrullDim_le_spanFinrank_maximalIdeal`
with `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`.

**I.6's valuation-ring maximality theorem** is exact in the pinned Mathlib.
Its two clauses are `LocalSubring.isMax_iff` and
`LocalSubring.exists_le_valuationSubring`; the `LocalSubring` order is precisely
domination. Theorem 6.2A is only partially upstream:
`IsDiscreteValuationRing.TFAE` and
`IsLocalRing.finrank_CotangentSpace_eq_one_iff` provide its algebraic core, but
a project wrapper must add Hartshorne's explicit dimension-one hypothesis and
regular-local clause. Open Mathlib PR #43655 may later simplify packaging the
local-ring image as a discrete valuation subring, but the roadmap does not rely
on it.

**I.3.9A and I.6.3A are not exact pinned-Mathlib results.**
`IsIntegralClosure.finite` and `IsIntegralClosure.isDedekindDomain` require a
finite separable extension; Hartshorne allows every finite extension. Open PR
[#41755](https://github.com/leanprover-community/mathlib4/pull/41755) contains
the nonseparable Krull–Akizuki core needed for Theorem 6.3A, but it is not in
the pinned checkout and does not prove Theorem 3.9A's module-finiteness. The
roadmap records it only as prior art. Pinned finite-support and Dedekind
valuation APIs do suffice for the independent two-chart proof of Lemma 6.5.

**Reformulation into scheme language.** Mathlib's `AlgebraicGeometry` namespace
covers much of Hartshorne Chapter II, and several results in Chapters III and IV
are the subject of open Mathlib pull requests. This project does not restate
Chapter I results scheme-theoretically and does not duplicate that work.

## Done means

A section counts as finished when every article listed for it satisfies all of:

1. the Lean statement compiles and the article records its name under `lean:`;
2. the proof compiles with no `sorry` and no `native_decide`;
3. `#print axioms` shows nothing beyond `propext`, `Classical.choice` and
   `Quot.sound`, which the `autoform verify` workflow checks on every pull
   request;
4. the statement has been read against the cited passage and matches it,
   including the standing hypothesis that `k` is algebraically closed and the
   convention that varieties are irreducible.

A scoped section or partial section counts as finished when all its articles
do. **The 163-leaf scope through Corollary 6.12 is finished.** Its 159 project
proofs compile, no proof contains `sorry` or `native_decide`, every
`#print axioms` is clean, and every statement has been read against its cited
passage; four further leaves are exact Mathlib results. Of the 50 §I.7 leaves,
47 are formalized and three remain.

Derived progress on the published site is computed from the dependency graph and
is not a claim about scope: a green node means its Lean proof compiles, not that
the section containing it is complete.

## What is not claimed

Section I.7 is not yet complete: its pure-curve degree and two reducible-curve
leaves remain. Section I.8 has been dispositioned claim by claim without
turning survey prose into proof specifications. The completion material later
in §I.5, Chapters II–V, and Appendices A–C remain deferred; unadopted exercises
and reference apparatus remain out of scope unless a later scope decision
changes their disposition.
Nothing in this repository should be read as formalizing "Hartshorne" or
"algebraic geometry" without the precise scope qualifier. The coverage
contract is terminal, but that means every inventoried unit is dispositioned;
it does not mean the three remaining §I.7 leaves or any deferred milestone is
proved.
