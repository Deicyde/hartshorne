---
article_id: af_6572c1c9f15a2e6280655f06
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projectiveSpace_smoothOfRelativeDimension_finiteTypeOverField
---

# Projective space is smooth

Let $k$ be a field and let $Y$ be a scheme of finite type over $\operatorname{Spec} k$.
For every $n$, the projection

$\mathbb{P}^n_k \times _{(\operatorname{Spec} k)} Y \to Y$,

canonically identified with $\mathbb{P}^n_Y \to Y$, is smooth of relative dimension $n$.

The finite-type hypothesis is retained to match Hartshorne's standing convention;
the arbitrary-base theorem proves the conclusion independently of that hypothesis.

## Depends on

- [Projective space is smooth over an arbitrary base](projective-space-smooth-arbitrary-base.md)
- [Projective space over a scheme](../../../schemes/proper-and-projective/projective-space-over-scheme.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne III.10, Example 10.0.1, p.268](../../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
