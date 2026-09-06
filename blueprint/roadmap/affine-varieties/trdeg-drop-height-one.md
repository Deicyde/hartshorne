---
declaration: theorem
origin: background
---

# A height-one prime drops the transcendence degree by one

Let `B` be a finitely generated domain over `k` and `𝔭 ⊆ B` a prime of height
one. Then `trdeg_k K(B/𝔭) = trdeg_k K(B) − 1`.

This is the heart of [the dimension formula](dim-formula-catenary.md). Once it
is available the general case follows by induction along a maximal chain below
`𝔭`, each step of which is a height-one prime in the quotient by the one below.

## The argument

Take a Noether normalisation `k[y₁,…,y_d] ⊆ B`, so `B` is integral over a
polynomial ring and `d = trdeg_k K(B)`. Let `𝔮 = 𝔭 ∩ k[y]`.

- `height 𝔮 = height 𝔭 = 1`, by
  [going down](going-down-integral.md) together with the fact that the fibres of
  an integral extension are zero-dimensional. This is the only step that is not
  formal, and it is the one Mathlib does not supply.
- A height-one prime of a UFD is principal, so `𝔮 = (f)` with `f` irreducible,
  and `k[y]/𝔮` has transcendence degree `d − 1` by
  [the hypersurface computation](polynomial-hypersurface-trdeg.md).
- `B/𝔭` is integral over `k[y]/𝔮`, so it has the same transcendence degree.

## Depends on

- [Going down for an integral extension of a normal domain](going-down-integral.md)
- [A hypersurface in affine space drops the transcendence degree by one](polynomial-hypersurface-trdeg.md)
- [Dimension of a finitely generated domain](dim-fg-domain.md)

## Proof depends on

- [Krull dimension is invariant under integral extensions](dimension-integral-extension.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)
