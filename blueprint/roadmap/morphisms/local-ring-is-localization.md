---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.localizationEquivLocalRing Hartshorne.coordToLocal Hartshorne.polyToLocal Hartshorne.isUnit_coordToLocal Hartshorne.coordToLocal_injective Hartshorne.localizationToLocal Hartshorne.localizationToLocal_surjective Hartshorne.ringKrullDim_localRingAt
---

# The local ring is a localisation

For an affine variety `Y` and a point `P`, `𝒪_{P,Y} ≅ A(Y)_{𝔪_P}`, and
consequently `dim 𝒪_P = height 𝔪_P`. This is the first half of Theorem 3.2(c).

The map is forced. A polynomial function has a germ at `P`; a polynomial not
vanishing at `P` has an invertible germ, since it is nonzero on a whole
neighbourhood and its reciprocal is regular there. So `A(Y) → 𝒪_P` inverts
everything outside `𝔪_P` and factors through the localisation.

Surjectivity is the definition of regular read backwards: a germ at `P` is `g/h`
on some neighbourhood with `h(P) ≠ 0`, and that datum *is* an element of
`A(Y)_{𝔪_P}`.

Injectivity is easier than Hartshorne's phrasing suggests. He works inside
`K(Y)`, where the identity principle is doing the work. Here it is not needed:
a germ is an equivalence class for "agree on the whole overlap", and a global
polynomial function with zero germ has domain all of `Y`, so it is zero
everywhere on the nose.

## What this does and does not give

`dim 𝒪_P = height 𝔪_P` is then free, since Mathlib computes the dimension of a
localisation at a prime as that prime's height
(`IsLocalization.AtPrime.ringKrullDim_eq_height`).

It is split from [the rest of 3.2(c) and (d)](affine-variety-rings.md) because
the two halves have different obstructions: this one needs no dimension theory
at all, while `height 𝔪_P = dim Y` needs
[the dimension formula](../affine-varieties/dim-formula-catenary.md).

## Depends on

- [The local ring at a point](local-ring.md)
- [The local ring is local](local-ring-is-local.md)
- [Points and maximal ideals](points-eq-maximal-ideals.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Sources

- [Hartshorne I.3, Theorem 3.2(c) (p. 17)](../../sources/hartshorne.md#i3)
