---
article_id: af_57089588ba2c404e80de35a7
declaration: theorem
origin: cited
lean: Hartshorne.exists_nonempty_open_smooth_of_isDominant Hartshorne.exists_nonempty_open_smoothOfRelativeDimension_of_isDominant
statement: formalized
proof: formalized
---

# Dominant maps are generically smooth on the source in characteristic zero

Let $f : X \to Y$ be a dominant morphism of integral finite-type schemes over
an algebraically closed field of characteristic zero. There is a nonempty open
$U$ in $X$ such that $U \to Y$ is smooth.

Shrinking $X$ and $Y$, we may assume both are nonsingular (II.8.16). In
characteristic zero $K(X)/K(Y)$ is separably generated (I.4.8A), so
$\Omega_{K(X)/K(Y)}$ has dimension $n = \dim X - \dim Y$ (II.8.6A). Hence
$\Omega_{X/Y}$ is locally free of rank $n$ on a nonempty open subset of $X$
(Ex. II.5.7), and $f$ is smooth there by Proposition 10.4.

## Depends on

- [Relative differentials of a smooth morphism](criteria/relative-differentials-rank-of-smooth.md)

## Proof depends on

- [Differentials of finitely generated field extensions](../../schemes/differentials/kaehler-differentials/field-differentials-dimension.md)
- Separably generated finitely generated extensions in characteristic zero.
- [The dense nonsingular locus](../../schemes/differentials/scheme-differentials/dense-nonsingular-locus.md)
- [The free locus of a coherent sheaf](../../schemes/coherent-sheaves/coherent-free-locus.md)
- [Smoothness by tangent-map surjectivity](smooth-iff-tangent-surjective.md)

## Sources

- [Hartshorne III.10, Lemma 10.5, p.271](../../../sources/hartshorne-iii-10.md#characteristic-zero-generic-smoothness-pp271272)
