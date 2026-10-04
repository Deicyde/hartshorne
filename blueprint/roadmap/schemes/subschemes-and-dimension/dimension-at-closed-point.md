---
article_id: af_b22063ac78ef7edd9e6fdd8c
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
statement: formalized
proof: formalized
lean: Hartshorne.dimension_at_closed_point
---

# Dimension at a closed point

Let `X` be an integral scheme of finite type over a field. For every closed point `P ∈ X`, `dim X = ringKrullDim 𝒪_{X,P}`.

Reduce to an affine neighbourhood of `P`. Identify the local-ring dimension with the height of the maximal prime and use the finite-type domain dimension theorem to identify that height with the global dimension.

## Depends on

- [Dimension of an affine scheme](affine-scheme-dimension.md)
- [Integral schemes](../first-properties/integral-scheme.md)
- [Morphisms of finite type](../first-properties/finite-type.md)

## Proof depends on

- The finite-type domain dimension formula and `ringKrullDim_stalk_eq_coheight`.

## Sources

- [Hartshorne II.3 (later-used-exercises)](../../../sources/hartshorne-ii-3.md#later-used-exercises)
