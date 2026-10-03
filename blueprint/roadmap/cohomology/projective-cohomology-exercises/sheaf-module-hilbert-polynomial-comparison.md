---
declaration: theorem
origin: cited
source_units: [chapter-iii-section-5]
not_ready: true
---

# Comparison with the graded-module Hilbert polynomial

Let `X=Pʳ_k`, `S=k[x₀,…,xᵣ]`, `F` coherent, and
`M=Γ_*(F)=⊕_(n:Z)H⁰(X,F(n))`. There is an integer `n₀` such that the
high-degree tail `M_≥n₀=⊕_(n≥n₀)H⁰(X,F(n))` is a finite graded
`S`-module. The coherent-sheaf Hilbert polynomial of `F` equals the
graded-module Hilbert polynomial of this tail, hence is independent of the
chosen sufficiently high truncation.

## Depends on

- [The coherent-sheaf Hilbert polynomial](coherent-sheaf-hilbert-polynomial.md)
- [The graded global-sections module](../../schemes/projective-sheaves/graded-global-sections-module.md)
- [Hilbert–Serre](../../intersections-projective-space/hilbert/hilbert-serre.md)

## Proof depends on

- [Serre vanishing](../projective-cohomology/serre-vanishing.md)
- [Eventual recovery from graded sections](../../schemes/projective-sheaves/proj-eventual-section-recovery.md)
- [Serre global generation](../../schemes/projective-sheaves/serre-global-generation.md)
- For large `n`, `χ(F(n))=dim_k H⁰(X,F(n))`.
- Finite generation of a high tail, as in Stacks Lemma 30.14.1, must be
  reconciled with the project's integer-graded truncation API; until then the
  comparison remains not ready.

## Sources

- [Hartshorne III, Exercise 5.2(b), p.230](../../../sources/hartshorne-iii-5.md#adopted-exercises-pp230233)
- [Stacks Project, Lemma 30.14.1, tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
