---
declaration: theorem
origin: bridged
source_units: [chapter-iii-section-10]
---

# The homogeneous action family is smooth

Let a group variety `G` act transitively on a homogeneous variety `X` over an
algebraically closed field of characteristic zero, let `Y` be nonsingular,
and let `f : Y -> X`. The action-family morphism

`h : G times Y -> X`,  `h(sigma,y) = sigma . f(y)`,

is smooth everywhere, of relative dimension

`dim G + dim Y - dim X`.

## Depends on

- [Algebraic group actions and homogeneous spaces](homogeneous-space-api.md)
- [Homogeneous spaces are nonsingular](homogeneous-spaces-regular.md)
- [Generic smoothness over the target](generic-smoothness-over-target.md)
- [Smooth relative-dimension calculus](smooth-relative-dimension-calculus.md)
- [Products of nonsingular varieties](../../schemes/differentials/differential-exercises/product-of-nonsingular-varieties.md)

## Proof depends on

- Apply generic smoothness to `h`, transport the resulting target open by
  compatible translations, and use orbit openness to cover `X`.
- Use the product regularity theorem to make the source of `h` nonsingular.

## Sources

- [Hartshorne III.10, first half of the proof of Theorem 10.8, p.273](../../../sources/hartshorne-iii-10.md#homogeneous-spaces-kleiman-and-bertini-pp272275)
