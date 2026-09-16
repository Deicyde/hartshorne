# Coverage contract

What this project claims, and what it does not. The source is Robin Hartshorne,
*Algebraic Geometry*, Springer GTM 52, 1977; see the
[source notes](../sources/hartshorne.md) for locators.

## In scope

Chapter I, sections 1 through 4, book pages 1–29:

| Section | Title | Pages | Articles | State |
| --- | --- | --- | --- | --- |
| I.1 | Affine Varieties | 1–8 | [23 articles](../roadmap/affine-varieties/README.md) | done |
| I.2 | Projective Varieties | 8–14 | [13 articles](../roadmap/projective-varieties/README.md) | done |
| I.3 | Morphisms | 14–23 | [32 articles](../roadmap/morphisms/README.md) | done |
| I.4 | Rational Maps | 24–29 | [13 articles](../roadmap/rational-maps/README.md) | decomposed, not yet proved |

All 68 articles of §§1–3 are done: 67 proved here and one already in Mathlib.
§4 is decomposed but carries no Lean yet, and no article in it claims otherwise.

The counts grow as the work goes on, almost always by splitting a node that
turned out to hold more than one pull request's worth of Lean; where the scope
itself widened, as it did for §4, this contract says so. The result-to-article
map in the source notes is the record of which numbered results ended up
where.

Every result the main text of those sections proves or uses is covered by an
article. Some articles carry more than one numbered result when they land
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

**One numbered result in these sections has no article.** Theorem 3.9A
(finiteness of integral closure, p. 20) is stated in §3 but used only by
exercises, which are out of scope. It is needed from §6 onward and will be
picked up whenever that scope is.

The first target was Corollary I.3.8, the arrow-reversing equivalence between
affine varieties over `k` and finitely generated integral domains over `k`. The
target of §4 is its birational counterpart, Theorem 4.4: varieties with dominant
rational maps are equivalent, arrows reversed, to finitely generated field
extensions of `k`.

## Out of scope

**Chapter I, sections 5 through 8, and Chapters II through V.** These are read
and located in the source notes so that a reader can see where §§1–4 sit, but
they carry no articles and nothing about them is claimed. They are located, not
planned: no dependency analysis has been done and no decomposition exists.

**The exercises of §4, and every exercise not listed above.** Hartshorne has
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

A section counts as finished when all its articles do. **§§1, 2 and 3 are
finished.** Every article in them compiles, no proof contains `sorry` or
`native_decide`, every `#print axioms` is clean, and every statement has been
read against its cited passage. §4 is not finished and is not claimed to be.

Derived progress on the published site is computed from the dependency graph and
is not a claim about scope: a green node means its Lean proof compiles, not that
the section containing it is complete.

## What is not claimed

No result outside §§1–4 is claimed, formalized, or planned. Nothing in this
repository should be read as formalizing "Hartshorne" or "algebraic geometry"
without the section qualifier. If the published site ever shows full progress,
that means §§1–4 are done and pages 30 through 420 of the book are untouched.
