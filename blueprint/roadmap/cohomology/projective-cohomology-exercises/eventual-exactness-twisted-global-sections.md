---
article_id: af_f4fd9a2b5afb357b2ea0fe1f
declaration: theorem
origin: cited
source_units: [chapter-iii-section-5]
---

# Eventual exactness of twisted global sections

Let `X` be projective over a Noetherian ring and let
`F₁→F₂→⋯→Fᵣ` be a finite exact sequence of coherent sheaves. There is
one integer `n₀` such that for every `n≥n₀`, the sequence

`Γ(X,F₁(n))→Γ(X,F₂(n))→⋯→Γ(X,Fᵣ(n))`

is exact at every position.

## Depends on

- [Global sections are left exact](../../schemes/sheaf-functors/global-sections-left-exact.md)
- [Twists and graded shifts](../../schemes/projective-sheaves/proj-twist-compatibility.md)

## Proof depends on

- [Serre vanishing](../projective-cohomology/serre-vanishing.md)
- [Abelian closure of quasi-coherent sheaves](../../schemes/modules-and-quasicoherent/quasicoherent-abelian-closure.md)
- Break the finite sequence into short exact sequences of coherent kernels
  and images, use `H¹` vanishing, and take the maximum of finitely many bounds.

## Sources

- [Hartshorne III, Exercise 5.10, p.233](../../../sources/hartshorne-iii-5.md#adopted-exercises-pp230233)
