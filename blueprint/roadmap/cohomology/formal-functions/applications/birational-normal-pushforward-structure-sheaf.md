---
declaration: isomorphism
origin: bridged
source_units: [chapter-iii-sections-11-12]
---

# Normal birational targets recover the structure sheaf

Let `f : X -> Y` be a birational projective morphism of Noetherian integral
schemes, with `Y` normal. Then the canonical unit map is an isomorphism

`O_Y ~= f_* O_X`.

This isolates the algebraic step in Hartshorne's proof of his connected-fibre
form of Zariski's Main Theorem.

## Depends on

- [Coherence of projective higher direct images](../../higher-direct-images/projective-higher-direct-images-coherent.md)
- [Affine opens have fraction field `K(X)`](../../../schemes/normalization-and-exercises/function-field-integral-scheme.md)
- [Normal schemes](../../../schemes/normalization-and-exercises/normal-scheme.md)

## Proof depends on

- Locally on `Y = Spec A`, the algebra
  `B = Gamma(Y, f_*O_X)` is finite over `A`.
- Birationality identifies the function fields of `X` and `Y`, embedding the
  integral domains `A` and `B` in that common field; normality makes `A`
  integrally closed, so `A = B`.

## Sources

- [Hartshorne III.11, proof of Corollary 11.4, p.280](../../../../sources/hartshorne-iii-11-12.md#applications-of-formal-functions-pp279281)
