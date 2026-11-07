# Orders via the normalization are lengths

## Status

New article from the projective-cycle-rational-equivalent-linear-space split (roadmap
proposal). No project Lean exists; nothing is recorded in the frontmatter. Formalize should
record declarations here only after independent review.

Source: Fulton, *Intersection Theory*, Example 1.2.3 (stated there for the order function
`ord_A(a) = ℓ_A(A/aA)` of a one-dimensional local domain), proved through Lemma A.3. The
finiteness hypothesis on the integral closure holds for local rings of varieties (normalization
of a variety over a field is finite).

## Existing Lean to build on

- Mathlib `Ring.ord` (`Mathlib/RingTheory/OrderOfVanishing/Basic.lean`, Stacks 02MD):
  `Ring.ord R x = Module.length R (R ⧸ Ideal.span {x})`, with `Ring.ord_mul`,
  `Ring.ordFrac`, and `Ring.ord_eq_addVal` for a DVR
  (`Mathlib/RingTheory/OrderOfVanishing/Noetherian.lean`). The left side of the article is
  `Ring.ord A a`; each summand's order is `Ring.ord (B_𝔪) a` = `addVal`.
- Mathlib `Module.length` and `Module.length_eq_add_of_exact`
  (`Mathlib/RingTheory/Length.lean`), `IsDedekindDomain` and the CRT decomposition of `B/aB`.
- `AlgebraicGeometry.Scheme.ord` (`Mathlib/AlgebraicGeometry/OrderOfVanishing.lean`) and
  `AlgebraicGeometry.Scheme.ord_eq_codimensionOneStalkValuation` (project) for the scheme side
  where the formula is applied.
- No Mathlib statement of the normalization formula was found.

## Candidate declarations (names are suggestions)

New module, say `Hartshorne.Intersection.NormalizationOrderLength`:

1. `Hartshorne.length_quotient_eq_length_quotient_of_finiteLength_cokernel`: for an injective
   `A`-linear `M → N` with finite-length cokernel and `a` a nonzerodivisor on both,
   `ℓ(M/aM) = ℓ(N/aN)` (snake lemma; the key step).
2. `Hartshorne.ord_eq_sum_ord_integralClosure`: the article's formula, with
   `[κ(𝔪):κ]` as `Module.finrank`.
