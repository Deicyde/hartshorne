---
article_id: af_55226f15d7959f3667585ad1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.vanishingIdeal_union Hartshorne.zeroLocus_vanishingIdeal_eq_closure
---

# The vanishing ideal

For $Y\subseteq\mathbb A^n$, its *vanishing ideal* is

$$I(Y)=\{f\in k[x_1,\ldots,x_n]: f(P)=0\text{ for every }P\in Y\}.$$

Hartshorne's Proposition I.1.2 records the following identities:

- $T_1\subseteq T_2$ implies $Z(T_1)\supseteq Z(T_2)$;
- $Y_1\subseteq Y_2$ implies $I(Y_1)\supseteq I(Y_2)$;
- $I(Y_1\cup Y_2)=I(Y_1)\cap I(Y_2)$;
- $Z(I(Y))=\overline Y$, the Zariski closure of $Y$.

The assignments $Z$ and $I$ form an inclusion-reversing Galois connection
between ideals of the polynomial ring and subsets of affine space.
The remaining identity $I(Z(\mathfrak a))=\sqrt{\mathfrak a}$ is
[the Nullstellensatz](nullstellensatz.md).

## Depends on

- [Algebraic sets](algebraic-set.md)
- [The Zariski topology on affine space](zariski-topology.md)

## Sources

- [Hartshorne I.1, definition of $I(Y)$ and Proposition 1.2 (p. 3)](../../sources/hartshorne.md#i1)
