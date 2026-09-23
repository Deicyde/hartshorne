---
schema: autoform-coverage/v2
artifact: sources/hartshorne.md
artifact_sha256: a7ab788edc610107f5250d28fa18456995e33a8b7fa09133ef90fcbd9f1606ec
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
| inventory-preamble | Bibliography and inventory policy | 1-18 | Source-notes preamble | 1a0bdb72f6d7513555284ac622b2aa22da84e192680edfef0f44dbf8b06d8015 | OUT | Project-authored bibliographic metadata and roadmap policy, not a standalone mathematical target |
| chapter-i-section-1 | Affine varieties | 19-49 | Chapter I §1, book pp. 1–8 | ce343b2db86774cdb86b8efcd433d223715fe44c0d2be865fe6d99ae864a1bfa | DECOMPOSED | [The affine coordinate ring](../roadmap/affine-varieties/affine-coordinate-ring.md), [Affine space is a Noetherian space](../roadmap/affine-varieties/affine-space-noetherian.md), [Affine and quasi-affine varieties](../roadmap/affine-varieties/affine-variety.md), [Algebraic sets](../roadmap/affine-varieties/algebraic-set.md), [Every finitely generated domain is a coordinate ring](../roadmap/affine-varieties/coordinate-ring-realization.md), [The dimension of affine space](../roadmap/affine-varieties/dim-affine-space.md), [Dimension is the dimension of the coordinate ring](../roadmap/affine-varieties/dim-eq-coordinate-ring-dim.md), [A finitely generated algebra over a field has finite dimension](../roadmap/affine-varieties/dim-fg-algebra-finite.md), [Dimension of a finitely generated domain](../roadmap/affine-varieties/dim-fg-domain.md), [The dimension formula for a finitely generated domain](../roadmap/affine-varieties/dim-formula-catenary.md), [One inequality of the dimension formula](../roadmap/affine-varieties/dim-formula-inequality.md), [Dimension of a quasi-affine variety](../roadmap/affine-varieties/dim-quasi-affine.md), [Dimension of a topological space and of a ring](../roadmap/affine-varieties/dimension.md), [Krull dimension is invariant under integral extensions](../roadmap/affine-varieties/dimension-integral-extension.md), [Height is preserved by contraction along an integral extension](../roadmap/affine-varieties/height-comap-integral.md), [Hypersurfaces and codimension one](../roadmap/affine-varieties/hypersurface-dimension.md), [Decomposition into irreducible components](../roadmap/affine-varieties/irreducible-decomposition.md), [Hilbert's Nullstellensatz](../roadmap/affine-varieties/nullstellensatz.md), [A hypersurface in affine space drops the transcendence degree by one](../roadmap/affine-varieties/polynomial-hypersurface-trdeg.md), [Algebraic sets and radical ideals](../roadmap/affine-varieties/radical-ideal-correspondence.md), [A height-one prime drops the transcendence degree by one](../roadmap/affine-varieties/trdeg-drop-height-one.md), [The vanishing ideal](../roadmap/affine-varieties/vanishing-ideal.md), [The Zariski topology on affine space](../roadmap/affine-varieties/zariski-topology.md) |
| chapter-i-section-2 | Projective varieties | 50-77 | Chapter I §2, book pp. 8–14 | 7d1de7f5186c3c491bcde17d14773f8bfb013439247df789e36fa29fbe050ac9 | DECOMPOSED | [Varieties are covered by affine pieces](../roadmap/projective-varieties/affine-cover.md), [Dimension of the homogeneous coordinate ring](../roadmap/projective-varieties/homogeneous-coordinate-ring-dimension.md), [Homogeneous ideals](../roadmap/projective-varieties/homogeneous-ideal.md), [Algebraic sets and homogeneous radical ideals](../roadmap/projective-varieties/homogeneous-ideal-correspondence.md), [The homogeneous vanishing ideal](../roadmap/projective-varieties/homogeneous-vanishing-ideal.md), [Projective algebraic sets](../roadmap/projective-varieties/projective-algebraic-set.md), [Dimension in projective space](../roadmap/projective-varieties/projective-dimension.md), [The homogeneous Nullstellensatz](../roadmap/projective-varieties/projective-nullstellensatz.md), [Projective space](../roadmap/projective-varieties/projective-space.md), [Projective space is a Noetherian space](../roadmap/projective-varieties/projective-space-noetherian.md), [Projective and quasi-projective varieties](../roadmap/projective-varieties/projective-variety.md), [The Zariski topology on projective space](../roadmap/projective-varieties/projective-zariski-topology.md), [The standard affine charts](../roadmap/projective-varieties/standard-affine-charts.md) |
| chapter-i-section-3 | Morphisms | 78-103 | Chapter I §3, book pp. 14–23, except Theorem 3.9A | f4da0c0a7240dbc99d6c481b930e8f40e9f55ed0caf8b3743f53724dec7e350d | DECOMPOSED | [Isomorphism via coordinate rings](../roadmap/morphisms/affine-iso-iff-algebra-iso.md), [Equivalence with finitely generated domains](../roadmap/morphisms/affine-variety-equivalence.md), [The local ring and function field of an affine variety](../roadmap/morphisms/affine-variety-rings.md), [The function field](../roadmap/morphisms/function-field.md), [The function field of an arbitrary variety](../roadmap/morphisms/function-field-abstract.md), [The function field is functorial for dominant morphisms](../roadmap/morphisms/function-field-functorial.md), [The underlying maps into germs and rational functions are injective](../roadmap/morphisms/function-field-injections.md), [The function field is the fraction field](../roadmap/morphisms/function-field-is-fraction-field.md), [The coordinate ring is the ring of regular functions](../roadmap/morphisms/global-regular-eq-coordinate-ring.md), [Global regular functions inside the function field](../roadmap/morphisms/global-functions/global-regular-in-function-field.md), [Global regular functions are the intersection of the local rings](../roadmap/morphisms/global-functions/global-regular-intersection-local-rings.md), [Morphisms into an affine variety](../roadmap/morphisms/hom-affine-bijection.md), [The local ring at a point](../roadmap/morphisms/local-ring.md), [The local ring is functorial](../roadmap/morphisms/local-ring-functorial.md), [The local ring is local](../roadmap/morphisms/local-ring-is-local.md), [The local ring is a localisation](../roadmap/morphisms/local-ring-is-localization.md), [Morphisms](../roadmap/morphisms/morphism.md), [Criterion for a morphism into an affine variety](../roadmap/morphisms/morphism-to-affine-criterion.md), [Points and maximal ideals](../roadmap/morphisms/points-eq-maximal-ideals.md), [The charts are isomorphisms of varieties](../roadmap/morphisms/projective-rings/chart-isomorphism.md), [Reading a global regular function on a chart](../roadmap/morphisms/projective-rings/chart-reading.md), [The degree bound](../roadmap/morphisms/projective-rings/degree-bound.md), [Graded localization](../roadmap/morphisms/projective-rings/graded-localization.md), [The homogeneous prime at a point](../roadmap/morphisms/projective-rings/point-ideal.md), [The function field of a projective variety](../roadmap/morphisms/projective-rings/projective-function-field.md), [The global regular functions of a projective variety](../roadmap/morphisms/projective-rings/projective-global-regular.md), [The local ring of a projective variety](../roadmap/morphisms/projective-rings/projective-local-ring.md), [An element stabilising a finite-dimensional subspace is integral](../roadmap/morphisms/projective-rings/stable-subspace.md), [Regular functions are continuous](../roadmap/morphisms/regular-function-continuous.md), [Regular functions on a quasi-affine variety](../roadmap/morphisms/regular-function-quasi-affine.md), [Regular functions on a quasi-projective variety](../roadmap/morphisms/regular-function-quasi-projective.md), [The ring of regular functions](../roadmap/morphisms/ring-of-regular-functions.md), [Varieties](../roadmap/morphisms/variety.md) |
| theorem-i-3-9a | Finiteness of integral closure | 104-105 | Chapter I, Theorem 3.9A, book p. 20 | 0f5341b4836456b2f4cf19a5574b3643e0799eac867daf6b74865bfdabff7920 | DEFERRED | Deferred with Theorem 6.3A to the normalization milestone beginning at Lemma 6.5; the approved opening of §6 does not use it |
| chapter-i-section-4 | Rational maps | 106-145 | Chapter I §4 running text and adopted prerequisites, book pp. 12, 13, 22, 24–29 | d0329b4f0e2285c3c2fba03d123f0bebdde1bc9ee20a311caa54418c1bac538f | DECOMPOSED | [Open affine sets are a base for the topology](../roadmap/rational-maps/affine-base.md), [The birational criterion](../roadmap/rational-maps/birational-criterion.md), [Birational varieties have isomorphic open subsets](../roadmap/rational-maps/birational-open-subsets.md), [Birational varieties have isomorphic function fields](../roadmap/rational-maps/birational-function-fields.md), [Every variety is birational to a hypersurface](../roadmap/rational-maps/birational-hypersurface.md), [Birational maps](../roadmap/rational-maps/birational-map.md), [Blowing up a point](../roadmap/rational-maps/blowing-up.md), [The complement of a hypersurface is affine](../roadmap/rational-maps/hypersurface-complement.md), [The graph hypersurface has localized coordinate ring](../roadmap/rational-maps/principal-open-coordinate-ring.md), [Morphisms agreeing on an open set](../roadmap/rational-maps/morphism-agreement.md), [Products of varieties](../roadmap/rational-maps/product-variety.md), [The projective closure of an affine variety](../roadmap/rational-maps/projective-closure.md), [Composition of dominant rational maps](../roadmap/rational-maps/rational-map-composition.md), [Rational maps](../roadmap/rational-maps/rational-map.md), [Rational maps and function fields](../roadmap/rational-maps/rational-map-function-field.md), [The Segre embedding](../roadmap/rational-maps/segre-embedding.md), [Separably generated field extensions](../roadmap/rational-maps/separably-generated.md) |
| chapter-i-section-5-geometry | Nonsingular varieties through Theorem 5.3 | 146-175 | Chapter I §5 from the opening definition through Theorem 5.3, book pp. 31–33 | ee362a68be872eca0b37655a6f2e2bea693cafb5441af3b14f55e0acdd17a6f1 | DECOMPOSED | [Regular local rings](../roadmap/nonsingular-varieties/regular-local-rings.md), [The cotangent-dimension bound](../roadmap/nonsingular-varieties/cotangent-dimension-bound.md), [Local rings are unchanged on open neighbourhoods](../roadmap/nonsingular-varieties/local-ring-open-invariance.md), [The cotangent space of affine space](../roadmap/nonsingular-varieties/ambient-cotangent-space.md), [The defining ideal and the local cotangent space](../roadmap/nonsingular-varieties/defining-ideal-cotangent-sequence.md), [Jacobian rank is independent of generators](../roadmap/nonsingular-varieties/jacobian-rank-invariance.md), [Nonsingular points of an affine variety](../roadmap/nonsingular-varieties/affine-nonsingular-points.md), [The Jacobian criterion](../roadmap/nonsingular-varieties/jacobian-criterion.md), [Intrinsic nonsingularity](../roadmap/nonsingular-varieties/intrinsic-nonsingularity.md), [The Jacobian rank bound](../roadmap/nonsingular-varieties/jacobian-rank-upper-bound.md), [Rank-drop loci are determinantal](../roadmap/nonsingular-varieties/determinantal-rank-locus.md), [The affine singular locus is closed](../roadmap/nonsingular-varieties/affine-singular-locus-closed.md), [Closedness from affine charts](../roadmap/nonsingular-varieties/singular-locus-closed.md), [An irreducible polynomial has a nonzero partial derivative](../roadmap/nonsingular-varieties/irreducible-polynomial-nonzero-partial.md), [An irreducible hypersurface has a nonsingular point](../roadmap/nonsingular-varieties/hypersurface-singular-locus-proper.md), [The singular locus is proper and closed](../roadmap/nonsingular-varieties/singular-locus.md) |
| chapter-i-section-5-completion | Completion and analytic local structure | 176-189 | Chapter I §5 after Theorem 5.3 through Examples 5.6.1–5.6.3, book pp. 33–35 | 16b6235edbcf411b8c62bddbc2c8662510e51d3c5d44c39fc756a20090eac7f2 | DEFERRED | Deferred pending a separately approved completion/Cohen milestone; these results are not needed for Theorems 5.1–5.3 |
| chapter-i-section-5-exercises | Elimination theory and §5 exercises | 190-200 | Chapter I Theorem 5.7A and Exercises 5.1–5.15, book pp. 35–39 | 2ac2976a7885e32ef668d86998813d14e82fe99f82efaa465490912eb3bc8e3e | OUT | Theorem 5.7A is introduced only for Exercise 5.15, and no §5 exercise is adopted by the approved main-text scope |
| chapter-i-section-6-valuations | Valuation rings, DVRs, and Dedekind localizations | 201-218 | Chapter I §6 through Theorem 6.2A and the following Dedekind observation, book pp. 39–40 | d95f1aabe45a6052ece774d833a09c3c7958407dcd0f9dafe2e864ef23bfcef0 | DECOMPOSED | [Curves](../roadmap/nonsingular-curves/curve.md), [Valuation rings are maximal local subrings](../roadmap/nonsingular-curves/valuation-ring-maximal-local-subring.md), [Every local subring is dominated by a valuation ring](../roadmap/nonsingular-curves/valuation-ring-dominates-local-subring.md), [Characterizations of discrete valuation rings](../roadmap/nonsingular-curves/dvr-characterizations.md), [Localizations of a Dedekind domain are DVRs](../roadmap/nonsingular-curves/dedekind-localization-dvr.md) |
| theorem-i-6-3a | Integral closure of a Dedekind domain | 219-224 | Chapter I, Theorem 6.3A, book p. 40 | 92db6853b451d3a60302d25214a71c7e4f20984a9a0d006e12f6291b27012c3d | DEFERRED | Deferred to the normalization milestone beginning at Lemma 6.5; the nearest pinned-Mathlib theorem assumes separability |
| chapter-i-section-6-local-structure | Local structure of nonsingular curves and point separation | 225-240 | Chapter I §6 after Theorem 6.3A through Lemma 6.4, book p. 41 | cdbb3e5cd21ef1196736f556ec852dd504586f4276b35c3733040351158e42c3 | DECOMPOSED | [Curves](../roadmap/nonsingular-curves/curve.md), [The function field is the fraction field of every local ring](../roadmap/nonsingular-curves/local-ring-fraction-field.md), [Dimension of the local ring of a variety](../roadmap/nonsingular-curves/local-ring-dimension.md), [Local rings of nonsingular curves are DVRs](../roadmap/nonsingular-curves/nonsingular-curve-local-ring-dvr.md), [Nonsingular curve points define discrete valuations](../roadmap/nonsingular-curves/nonsingular-curve-valuation.md), [Linear fractions separate projective points](../roadmap/nonsingular-curves/projective-linear-separation.md), [Membership of a homogeneous fraction in a local ring](../roadmap/nonsingular-curves/homogeneous-fraction-local-membership.md), [The local ring determines the point](../roadmap/nonsingular-curves/local-ring-inclusion-determines-point.md) |
| chapter-i-section-6-projective-model | Normalization, valuation-space curves, and projective models | 241-254 | Chapter I §6, Lemma 6.5 through Corollary 6.12, book pp. 41–45 | a926344f22da69a8e94a9b381a63ef06eea7ce03e90f8a0be50f16c500ffb34f | DEFERRED | Deferred to later normalization and projective-model milestones after Theorems 3.9A and 6.3A |
| chapter-i-section-6-exercises | Exercises on curves and valuations | 255-260 | Chapter I, Exercises 6.1–6.7, book pp. 46–47 | c437637a4ad44956654aeaedaed7173e3b1381ebe0cc9807359206ab13559595 | OUT | No §6 exercise is used by the approved opening through Lemma 6.4 |
| remaining-sections | Undecomposed remainder of the book | 261-274 | Chapter I §§7–8 and Chapters II–V, book pp. 47–420 | 00ceefe5dcbf4668bdc2abd0f2bfd445cf0e428435bffb0bfbd49e4bf6cd5ef6 | OUT | Explicitly outside the current scope; the inventory only locates these sections |
| standing-conventions | Algebraically closed base field and irreducible varieties | 275-282 | Standing conventions for Chapter I | 32c55ea4bf211d1ee39edc51f124ebc7e3841b0728a82001ac113c4cff8be7df | DECOMPOSED | [Affine and quasi-affine varieties](../roadmap/affine-varieties/affine-variety.md), [Projective and quasi-projective varieties](../roadmap/projective-varieties/projective-variety.md), [Varieties](../roadmap/morphisms/variety.md) |

## In scope

Chapter I, sections 1 through 4 (book pages 1–29), the geometric core of
section 5 through Theorem 5.3 (book pages 31–33), and the opening local-
structure milestone of section 6 through Lemma 6.4 (book pages 39–41):

| Section | Title | Pages | Articles | State |
| --- | --- | --- | --- | --- |
| I.1 | Affine Varieties | 1–8 | [23 articles](../roadmap/affine-varieties/README.md) | done |
| I.2 | Projective Varieties | 8–14 | [13 articles](../roadmap/projective-varieties/README.md) | done |
| I.3 | Morphisms | 14–23 | [33 articles](../roadmap/morphisms/README.md) | done |
| I.4 | Rational Maps | 24–29 | [17 articles](../roadmap/rational-maps/README.md) | done |
| I.5 through Thm. 5.3 | Nonsingular Varieties | 31–33 | [16 articles](../roadmap/nonsingular-varieties/README.md) | done |
| I.6 through Lem. 6.4, excluding Thm. 6.3A | Local Structure of Nonsingular Curves | 39–41 | [12 articles](../roadmap/nonsingular-curves/README.md) | planned |

All 86 articles in §§1–4 are done: 85 are proved here and one was already in
Mathlib. The §4 results include the rational-map core through Corollary 4.5,
separability, projective closure, the Segre/product construction, the
hypersurface normal form, and blowing up. The approved part of §5 adds 16
articles: Mathlib supplies the exact regular-local/cotangent criterion, and the
other 15 are proved here. Thus all 102 scoped targets are complete: 100 are
proved in this project and two are supplied by Mathlib.

The approved opening of §6 adds 12 targets. Mathlib supplies the two clauses of
Theorem 6.1A exactly; the other ten targets remain to be formalized. The expanded
roadmap therefore has 114 leaves, of which 104 are complete.

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

**Two quoted integral-closure results remain deferred.** Theorem 3.9A
(finiteness of integral closure, p. 20) is not used before Lemma 6.5. Theorem
6.3A is likewise first used there. They will enter together with the
normalization and valuation-space milestone, not the approved opening through
Lemma 6.4.

The first target was Corollary I.3.8, the arrow-reversing equivalence between
affine varieties over `k` and finitely generated integral domains over `k`.
Theorem 4.4 is its birational counterpart: varieties with dominant rational
maps are equivalent, arrows reversed, to finitely generated field extensions of
`k`. The declared §4 scope continues through Proposition 4.9 and the blow-up
construction on pages 28–29. The §5 milestone develops the Jacobian criterion
and ends with Theorem 5.3, that the singular locus is a proper closed subset;
that milestone is now complete. The next milestone identifies the local rings
of nonsingular curves as DVRs and proves Lemma 6.4, that inclusion of local
rings inside the function field determines the point.

## Deferred and out of scope

**The rest of §5 after Theorem 5.3.** Completion, Theorems 5.4A and 5.5A, and
analytic isomorphism through Examples 5.6.1–5.6.3 are deferred to a separately
approved completion milestone. Theorem 5.7A is out of scope because it is
introduced only for Exercise 5.15.

**The rest of Chapter I §6.** Theorem 6.3A and Lemma 6.5 through Corollary
6.12 are deferred to normalization, valuation-space, and projective-model
milestones. The exercises are out of scope.

**Chapter I, sections 7 through 8, and Chapters II through V.** These are read
and located in the source notes, but they carry no articles and nothing about
them is claimed. They are located, not planned: no dependency analysis has
been done and no decomposition exists.

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
do. **§§1–4 and the approved part of §5 are finished.** The completed articles
compile, no proof contains `sorry` or
`native_decide`, every `#print axioms` is clean, and every statement has been
read against its cited passage. **The approved opening of §6 is planned but not
finished.**

Derived progress on the published site is computed from the dependency graph and
is not a claim about scope: a green node means its Lean proof compiles, not that
the section containing it is complete.

## What is not claimed

No result after Lemma 6.4 is currently claimed. The completion material later
in §5 is explicitly deferred; so are Theorems 3.9A and 6.3A and the remainder
of §6. The unadopted exercises, §7 onward, and Chapters II–V are out. Nothing in
this repository should be read as formalizing "Hartshorne" or "algebraic
geometry" without the precise scope qualifier. Full progress means only that
the declared scope through Lemma 6.4 is complete.
