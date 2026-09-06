---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.height_maximalIdealAt_eq Hartshorne.ringKrullDim_localRingAt_eq_dim
---

# The local ring and function field of an affine variety

Let `Y ⊆ 𝔸ⁿ` be an affine variety with coordinate ring `A(Y)`. Then

- `𝒪_P ≅ A(Y)_{𝔪_P}`, and `dim 𝒪_P = dim Y` (Theorem 3.2(c));
- `K(Y)` is the fraction field of `A(Y)`, a finitely generated field extension
  of `k` of transcendence degree `dim Y` (Theorem 3.2(d)).

These are the two parts of Theorem 3.2 that are about the *local* rings rather
than the global one. The first two parts are separate nodes:
[`𝒪(Y) ≅ A(Y)`](global-regular-eq-coordinate-ring.md) and
[points ↔ maximal ideals](points-eq-maximal-ideals.md), both proved.

`𝒪_P ≅ A(Y)_{𝔪_P}` is the injectivity of `α : A(Y) → 𝒪(Y)` together with
surjectivity straight from the definition of regular: a germ at `P` is `g/h` with
`h(P) ≠ 0`, which is exactly an element of the localisation. The dimension claim
is `dim 𝒪_P = height 𝔪_P` together with Theorem 1.8A. Part (d) follows from (c)
at the generic point, or directly from `α` being injective with the right image.

Together with the first two parts this is the main theorem of the section: the
coordinate ring already knows everything about an affine variety, and that is
what makes the equivalence of categories at the end of the chapter possible.

## Status

Complete. The localisation clause of (c) is
[its own node](local-ring-is-localization.md), together with
`dim 𝒪_P = height 𝔪_P`, and part (d) is
[another](function-field-is-fraction-field.md).

The clause that stayed open longest was `height 𝔪_P = dim Y`, which is
[the dimension formula](../affine-varieties/dim-formula-catenary.md) applied to
a maximal ideal: the quotient by a maximal ideal is a field, so it contributes
nothing to the formula and the height absorbs the whole dimension. Proposition
1.7 then turns `dim A(Y)` into `dim Y`.

That the last piece of §3 to fall was a clause of Theorem 1.8A, quoted by
Hartshorne without proof, is worth noting: the geometry of the section was
finished well before the commutative algebra it rests on.

## Depends on

- [The local ring at a point](local-ring.md)
- [The local ring is local](local-ring-is-local.md)
- [The function field](function-field.md)
- [The three rings embed in the function field](function-field-injections.md)
- [The coordinate ring is the ring of regular functions](global-regular-eq-coordinate-ring.md)
- [Points and maximal ideals](points-eq-maximal-ideals.md)
- [The local ring is a localisation](local-ring-is-localization.md)
- [The function field is the fraction field](function-field-is-fraction-field.md)

## Proof depends on

- [Dimension is the dimension of the coordinate ring](../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [Dimension of a finitely generated domain](../affine-varieties/dim-fg-domain.md)
- [The dimension formula for a finitely generated domain](../affine-varieties/dim-formula-catenary.md)

## Sources

- [Hartshorne I.3, Theorem 3.2 (p. 17)](../../sources/hartshorne.md#i3)
