---
article_id: af_d0979ec4ff20812bcce7511f
declaration: definition
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.weilDivisorProjectiveDegree Hartshorne.weilDivisorProjectiveDegree_of_primeDivisor Hartshorne.primeDivisorProjectiveDegree Hartshorne.projectiveSpectrumPointDegree_cast
---

# Degree of a projective Weil divisor

Let $k$ be algebraically closed and let $X \subseteq \mathbb{P}^n_k$ be a projective variety
nonsingular in codimension one. For a Weil divisor $D = \sum _i n_i Y_i$ on
$X$, define

$\deg D = \sum _i n_i \cdot \deg Y_i$,

where each prime divisor is given its projective degree in the fixed
embedding of $X$.

The same formula defines the degree for any closed subscheme $X$ of $\mathbb{P}^n_k$;
the hypotheses that $X$ is a variety nonsingular in codimension one serve only to make
$\operatorname{Div} X$ the divisor group of Hartshorne's §6.

This is the preamble of Exercise 6.2. The unique completion criterion is the
additive degree homomorphism $\operatorname{Div} X \to Z$; its invariance under linear
equivalence belongs to the excluded part (d), not to this node.

## Depends on

- [The Weil divisor group](../weil-divisors/weil-divisor-group.md)
- [Projective Hilbert polynomial and degree](../../../intersections-projective-space/hilbert/projective-hilbert-polynomial-and-degree.md)

## Sources

- [Hartshorne II.6, degree definition in the preamble to Exercise 6.2 on printed p.146](../../../../sources/hartshorne-ii-6.md#adopted-exercises-and-later-use-evidence)
