---
article_id: af_0463158229157ce9dfe951a4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.SmoothTangent.smoothOfRelativeDimension_tfae_of_isRegularAt
---

# Smoothness by tangent-map surjectivity

Let $f : X \to Y$ be a morphism of nonsingular varieties over an algebraically
closed field, and assume $\dim X = \dim Y + n$. The following are equivalent:

1. $f$ is smooth of relative dimension $n$;
2. $\Omega_{X/Y}$ is locally free of rank $n$;
3. for every closed $x \in X$, the Zariski tangent map at $x$ is surjective.

## Depends on

- [Relative differentials of a smooth morphism](criteria/relative-differentials-rank-of-smooth.md)
- [The Zariski tangent map](zariski-tangent-map.md)
- [The non-zero-divisor local criterion for flatness](local-flatness-nonzerodivisor-criterion.md)
- [Smoothness and regularity over an algebraically closed field](criteria/smooth-over-algebraically-closed-iff-regular.md)

## Proof depends on

- [The transitivity sequence for differential sheaves](../../schemes/differentials/scheme-differentials/relative-differentials-transitivity.md)
- [Fibre dimension of a coherent sheaf is upper semicontinuous](../semicontinuity/foundations/coherent-fiber-dimension-upper-semicontinuous.md)
- Regular systems of parameters in regular local rings and iteration of the
  local flatness criterion.

## Sources

- [Hartshorne III.10, Proposition 10.4, pp.270–271](../../../sources/hartshorne-iii-10.md#tangent-criterion-pp270271)
