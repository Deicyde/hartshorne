---
declaration: theorem
origin: cited
source_units: [chapter-iii-section-10]
---

# Smoothness and geometrically regular fibres

Let `f : X -> Y` be a morphism of finite-type schemes over a field. Then `f`
is smooth of relative dimension `n` if and only if it is flat and, for every
`y : Y`, the fibre after base change to an algebraic closure of `k(y)` is
regular and equidimensional of dimension `n`.

## Depends on

- [Smoothness and regularity over an algebraically closed field](smooth-over-algebraically-closed-iff-regular.md)
- [Smooth relative-dimension calculus](smooth-relative-dimension-calculus.md)
- [The fibre of a morphism](../../schemes/fiber-products/scheme-fiber.md)

## Proof depends on

- `AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField` from pinned
  Mathlib, after comparing smooth fibres with geometrically regular fibres.
- Faithfully flat descent of local freeness of Kähler differentials along an
  algebraic closure of a residue field.

## Sources

- [Hartshorne III.10, Theorem 10.2, pp.269–270](../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
- [Stacks Project, Lemma 29.35.3, tag 01V8](../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
