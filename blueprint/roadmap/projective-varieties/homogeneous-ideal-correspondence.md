---
article_id: af_0e77b22f571f2b7eaeff25ed
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.homogeneousVanishingIdeal_projZeroSet Hartshorne.isIrreducible_iff_isPrime_homogeneousVanishingIdeal
---

# Algebraic sets and homogeneous radical ideals

$Y \mapsto J(Y)$ and $\mathfrak{a} \mapsto Z(\mathfrak{a} )$ are mutually inverse, inclusion-reversing bijections
between the algebraic sets of $\mathbb{P} ^{n}$ and the homogeneous radical ideals of $S$
other than the irrelevant ideal $S_{+}$. An algebraic set is irreducible if and
only if its homogeneous ideal is prime, and $\mathbb{P} ^{n}$ itself is irreducible
(Exercise 2.4).

This is the projective form of [Corollary I.1.4](../affine-varieties/radical-ideal-correspondence.md), and the proof follows it once the
homogeneous Nullstellensatz supplies $J(Z(\mathfrak{a} )) = \sqrt{\mathfrak{a}}$ for $Z(\mathfrak{a} ) \ne \varnothing$. The
irreducible-iff-prime half uses that primeness of a homogeneous ideal can be
tested on homogeneous elements, which is why the graded background node comes
first.

The exclusion of $S_{+}$ is the one genuine difference from the affine case and the
usual source of off-by-one errors: $S_{+}$ is a homogeneous radical ideal with
$Z(S_{+}) = \varnothing$, and $\varnothing$ already corresponds to $S$.

Exercise 2.2 belongs here rather than with the Nullstellensatz: $Z(\mathfrak{a} ) = \varnothing$ if
and only if $\sqrt{\mathfrak{a}}$ is $S$ or $S_{+}$, equivalently $\mathfrak{a} \supseteq S_d$ for some $d > 0$. That
is exactly the criterion deciding which homogeneous radical ideals this
correspondence must leave out, and it is not needed to prove Exercise 2.1.

## Depends on

- [The homogeneous vanishing ideal](homogeneous-vanishing-ideal.md)
- [The homogeneous Nullstellensatz](projective-nullstellensatz.md)
- [Homogeneous ideals](homogeneous-ideal.md)

## Sources

- [Hartshorne I.2, Exercise 2.4 (p. 11)](../../sources/hartshorne.md#i2)
