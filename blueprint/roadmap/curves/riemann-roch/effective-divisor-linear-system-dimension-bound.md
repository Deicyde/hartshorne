---
article_id: af_e57814eb743c332e5f11b056
declaration: theorem
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# The dimension bound for an effective divisor

Let `D` be an effective divisor on a Chapter IV curve of genus `g`. Then

`dim|D| <= deg D`.

Equality holds if and only if `D=0` or `g=0`. The dimension is integer-valued;
for an effective divisor the system is nonempty, so no truncation ambiguity
occurs in the displayed inequality.

## Depends on

- [Divisor sections and complete linear systems](curve-divisor-sections.md)
- [The point-divisor exact sequence](point-divisor-exact-sequence.md)
- [The Riemann–Roch theorem](riemann-roch.md)
- [Genus zero characterizes the projective line](genus-zero-iff-projective-line.md)

## Proof depends on

- Induction on the degree using the point-divisor exact sequence bounds the
  increase of `l(D)` by one at each point.
- Analyze equality using Riemann–Roch and the genus-zero classification.

## Sources

- [Hartshorne IV.1, Exercise 1.5, p.298](../../../sources/hartshorne-iv-1.md#exercise-disposition-printed-pp297298)
