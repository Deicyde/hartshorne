---
article_id: af_ed89215a4d06659a130c6da1
---

# Local structure of nonsingular curves

Hartshorne's study of curves starts with a valuation-theoretic description of
their local rings. A curve is a variety of dimension one. At a nonsingular
point its local ring is Noetherian, local, a domain, regular, and one-
dimensional; Theorem 6.2A says precisely that such a ring is a discrete
valuation ring. Its image in the function field is therefore a valuation ring
of `K(Y)/k`.

The second result in this milestone is Lemma 6.4. For a quasi-projective variety
`Y`, inclusion `𝒪_{Q,Y} ⊆ 𝒪_{P,Y}` inside `K(Y)` forces `P = Q`. Hartshorne
puts the two points into a common affine chart. The Lean proof uses an equivalent
projective separation argument: choose a homogeneous linear fraction regular at
`Q` but not at `P`. This keeps the full source statement while fitting the
project's existing projective function-field API.

## Mathlib boundary

The pinned Mathlib exactly proves both clauses of Theorem 6.1A as
`LocalSubring.isMax_iff` and `LocalSubring.exists_le_valuationSubring`.
Its `IsDiscreteValuationRing.TFAE` contains most of Theorem 6.2A, but not the
source's exact four-way statement involving `IsRegularLocalRing` under an
explicit dimension-one hypothesis, so that theorem remains a small project
wrapper.

Open Mathlib PR
[#43655](https://github.com/leanprover-community/mathlib4/pull/43655) develops
discreteness for equivalent valuations and may later simplify the valuation-
subring packaging. Open PRs #28683 and #29574 overlap the missing generic fact
that a regular local ring is a domain. The roadmap targets only the pinned
checkout and does not assume any of these PRs merge.

## Valuation and DVR background

- [Valuation rings are maximal local subrings](valuation-ring-maximal-local-subring.md)
- [Every local subring is dominated by a valuation ring](valuation-ring-dominates-local-subring.md)
- [Characterizations of discrete valuation rings](dvr-characterizations.md)
- [Localizations of a Dedekind domain are DVRs](dedekind-localization-dvr.md)

## Curves and their local rings

- [Curves](curve.md)
- [The function field is the fraction field of every local ring](local-ring-fraction-field.md)
- [Dimension of the local ring of a variety](local-ring-dimension.md)
- [Local rings of nonsingular curves are DVRs](nonsingular-curve-local-ring-dvr.md)
- [Nonsingular curve points define discrete valuations](nonsingular-curve-valuation.md)

## The local ring determines the point

- [Linear fractions separate projective points](projective-linear-separation.md)
- [Membership of a homogeneous fraction in a local ring](homogeneous-fraction-local-membership.md)
- [The local ring determines the point](local-ring-inclusion-determines-point.md)

## Scope note

This milestone stops after Lemma 6.4 on printed p. 41. Theorem 6.3A is
explicitly deferred because it is first used in Lemma 6.5, where it combines
with the already deferred Theorem 3.9A. Lemma 6.5 through Corollary 6.12 form a
later normalization, valuation-space, and projective-model milestone. The §6
exercises remain out of scope.
