---
declaration: theorem
origin: cited
source_units: [chapter-iii-section-10]
---

# Étale, flat-unramified, and differential criteria

Let `f : X -> Y` be a morphism of schemes of finite type over a field. Define
Hartshorne-unramified to mean that for every `x : X`, with `y=f(x)`,

`m_y O_{X,x} = m_x`

and `k(x)/k(y)` is separable algebraic. Then the following are equivalent:

1. `f` is étale, equivalently smooth of relative dimension zero;
2. `f` is flat and `Omega[X/Y]=0`;
3. `f` is flat and Hartshorne-unramified.

This source-shaped TFAE is a project wrapper around several exact Mathlib
results and is not itself marked `mathlib: true`.

## Depends on

- [The relative differential sheaf](../../schemes/differentials/scheme-differentials/relative-differentials.md)
- [The stalk criterion for flat morphisms](../flat-families/flatness/flat-morphism-stalk-criterion.md)

## Proof depends on

- `AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero` and
  `Etale.iff_flat_and_formallyUnramified` in pinned Mathlib.
- `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`, including residue-field
  separability, applied to every stalk map.

## Sources

- [Hartshorne III.10, Exercise 10.3, p.275](../../../sources/hartshorne-iii-10.md#exercise-disposition-pp275276)
- [Stacks Project, Lemma 29.37.15, tag 02GU](../../../sources/hartshorne-iii-10.md#exercise-disposition-pp275276)
