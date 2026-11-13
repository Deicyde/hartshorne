---
article_id: af_65a92cc584948964142a20b3
declaration: theorem
origin: cited
lean: Hartshorne.LinearSystem.exists_dim_complete_nsmul_eq_projectiveHilbertPolynomial Hartshorne.LinearSystem.exists_dim_complete_weil_nsmul_eq_projectiveHilbertPolynomial Hartshorne.VeryAmpleHilbert.classicalPoint Hartshorne.VeryAmpleHilbert.mem_projZeroSet_iff_classicalPoint_mem_range
statement: formalized
proof: formalized
---

# Very ample linear systems and the Hilbert polynomial

Let $D$ be a very ample divisor on a nonsingular projective variety and use
its complete linear system to embed $X$ in projective space. For every
sufficiently large $n$,

$\dim |nD| = P_X(n) - 1$,

where $P_X$ is the Hilbert polynomial of this embedding.

The proof works for any closed embedding over the ground field whose pullback of
$\mathcal{O}(1)$ is $\mathcal{O}_X(D)$ and, for Cartier divisors, without nonsingularity; the
hypotheses are kept because they are Hartshorne's setting.

## Depends on

- [Linear systems](linear-system-api.md)
- [Hilbert polynomials and degrees of projective algebraic sets](../../../intersections-projective-space/hilbert/projective-hilbert-polynomial-and-degree.md)

## Proof depends on

- Eventual surjectivity from ambient homogeneous polynomials to the global
  sections of $\mathcal{O}_X(n)$.
- [Eventual recovery from graded sections](../../projective-sheaves/proj-eventual-section-recovery.md)
- [The scheme-theoretic image of a reduced source](../../subschemes-and-dimension/scheme-theoretic-image-reduced-source.md)

## Sources

- [Hartshorne II.7, Exercise 7.6(a) (p.170)](../../../../sources/hartshorne-ii-7.md#adopted-exercises)
