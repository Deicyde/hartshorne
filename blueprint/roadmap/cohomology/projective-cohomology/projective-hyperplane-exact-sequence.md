---
article_id: af_363afc5bb951feaadf99ac85
declaration: short exact sequence
origin: cited
source_units: [chapter-iii-section-5]
---

# The hyperplane exact-sequence bridge

Let `H=V₊(xᵣ)⊆Pʳ_A`, identified with `Pʳ⁻¹_A`, and let `i:H→Pʳ_A`
be the closed immersion. Multiplication by `xᵣ`, restriction, and the chosen
twist identifications form a natural graded short exact sequence

`0 ⟶ ⊕_n O_X(n-1) ⟶ ⊕_n O_X(n) ⟶ i_*(⊕_n O_H(n)) ⟶ 0`.

The first map is degree zero after shifting, and the resulting cohomology map
is multiplication by `xᵣ` under the graded Čech identifications.

## Depends on

- [Twists and graded shifts](../../schemes/projective-sheaves/proj-twist-compatibility.md)
- [Closed extension by zero](../../schemes/sheaf-functors/closed-extension-by-zero.md)

## Proof depends on

- [The long exact sequence of sheaf cohomology](../sheaf-cohomology/sheaf-cohomology-long-exact-sequence.md)
- [Closed pushforward preserves cohomology](../sheaf-cohomology/closed-pushforward-cohomology.md)
- Exactness of sheafification of `0→S(-1)→S→S/(xᵣ)→0`.

## Sources

- [Hartshorne III.5, proof of Theorem 5.1(b), p.227](../../../sources/hartshorne-iii-5.md#cohomology-of-twists-pp225228)
