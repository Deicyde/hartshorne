# Coverage contract

What this project claims, and what it does not. The source is Robin Hartshorne,
*Algebraic Geometry*, Springer GTM 52, 1977; see the
[source notes](../sources/hartshorne.md) for locators.

## In scope

Chapter I, sections 1 through 3, book pages 1–23:

| Section | Title | Pages | Articles |
| --- | --- | --- | --- |
| I.1 | Affine Varieties | 1–8 | [23 articles](../roadmap/affine-varieties/README.md) |
| I.2 | Projective Varieties | 8–14 | [13 articles](../roadmap/projective-varieties/README.md) |
| I.3 | Morphisms | 14–23 | [32 articles](../roadmap/morphisms/README.md) |

All 68 are done: 67 proved here and one already in Mathlib. The counts have
grown as the work went on, always by splitting a node that turned out to hold
more than one pull request's worth of Lean, never by widening the scope; the
result-to-article map in the source notes is the record of which numbered
results ended up where.

Every result the main text of those sections proves or uses is covered by an
article. Some articles carry more than one numbered result when they land
together: Propositions 1.5 and 1.6 share one, and Theorem 1.11A, Proposition
1.12A and Proposition 1.13 share another. The
[source notes](../sources/hartshorne.md) give the result-to-article map.

Exercises 2.1–2.7 are covered too, because Hartshorne states the projective
Nullstellensatz, the homogeneous ideal correspondence, and both projective
dimension computations as exercises and then relies on them in later sections;
leaving them out would make §3 rest on unstated results.

**One numbered result in these sections has no article.** Theorem 3.9A
(finiteness of integral closure, p. 20) is stated in §3 but used only by
exercises, which are out of scope. It is needed from §6 onward and will be
picked up whenever that scope is.

The chapter target is Corollary I.3.8, the arrow-reversing equivalence between
affine varieties over `k` and finitely generated integral domains over `k`.

## Out of scope

**Chapter I, sections 4 through 8, and Chapters II through V.** These are read
and located in the source notes so that a reader can see where §§1–3 sit, but
they carry no articles and nothing about them is claimed. They are located, not
planned: no dependency analysis has been done and no decomposition exists.

**The exercises, apart from 2.1–2.7.** Hartshorne has more than four hundred
exercises. The seven adopted above are adopted because the main text depends on
them, and that is the only criterion applied.

**Results Hartshorne quotes without proof.** Statements he numbers with a
trailing `A` are commutative algebra imported from Atiyah–Macdonald, Matsumura
and Zariski–Samuel. They carry `origin: background` and are prerequisites rather
than claims against the source. Where the pinned Mathlib already proves one, the
article records the upstream declaration and the work is to check that the
statement matches. Checked against the pinned checkout:

- **I.1.3A**, Hilbert's Nullstellensatz, is
  `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`, under
  `[IsAlgClosed K] [Finite σ]`. Hartshorne's case is the specialisation `K = k`.
  This is the one article in the project asserting `mathlib: true`.
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

The chapter counts as finished when all three sections do. Derived progress on
the published site is computed from the dependency graph and is not a claim
about scope: a green node means its Lean proof compiles, not that the section
containing it is complete.

## What is not claimed

No result outside §§1–3 is claimed, formalized, or planned. Nothing in this
repository should be read as formalizing "Hartshorne" or "algebraic geometry"
without the section qualifier. If the published site ever shows full progress,
that means §§1–3 are done and pages 24 through 420 of the book are untouched.
