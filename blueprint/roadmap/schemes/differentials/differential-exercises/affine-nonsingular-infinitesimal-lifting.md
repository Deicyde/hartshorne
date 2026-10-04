---
article_id: af_84d5f368413d6cf560e50055
declaration: theorem
origin: cited
source_units: [chapter-ii-section-8]
---

# Infinitesimal lifting for a nonsingular affine scheme

Let `k` be algebraically closed and let `A` be a finitely generated
`k`-algebra such that `Spec A` is nonsingular. For every surjection of
`k`-algebras `B' -> B` with square-zero kernel and every `k`-algebra map
`A -> B`, there is a lift `A -> B'`.

## Depends on

- [The conormal sequence for a nonsingular closed immersion](../scheme-differentials/nonsingular-closed-immersion-conormal.md)
- [Differentials characterize nonsingularity](../scheme-differentials/differentials-characterize-nonsingular.md)

## Proof depends on

- Embed `A` as a quotient of a polynomial algebra and split the resulting
  conormal sequence after applying `Hom(-, I)`.
- `Algebra.FormallySmooth.liftOfSurjective` in
  `Mathlib/RingTheory/Smooth/Basic.lean` supplies the final lift once formal
  smoothness has been established from the source hypotheses.

## Sources

- [Hartshorne II.8, Exercise 8.6 (pp.188–189)](../../../../sources/hartshorne-ii-8.md#adopted-exercises-and-later-use-evidence)
