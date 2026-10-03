---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Fibre cohomology dimension is upper semicontinuous

Let `f : X -> Y` be a projective morphism of Noetherian schemes and let `F`
be a coherent `O_X`-module flat over `Y`. For every `i >= 0`, the function

`y |-> dim_(k(y)) H^i(X_y, F_y)`

is upper semicontinuous on `Y`.

## Depends on

- [Fibre dimension of a coherent sheaf is upper semicontinuous](coherent-fiber-dimension-upper-semicontinuous.md)
- [A finite-free model for projective cohomology](../finite-free-complex/projective-cohomology-finite-free-model.md)
- [Fibre cohomology as residue-field tensor cohomology](../../flat-families/families-hilbert/fiber-cohomology-residue-field-tensor.md)

## Proof depends on

- After restricting to `Y = Spec A`, the finite-free model gives a four-term
  exact sequence whose dimension formula expresses `h^i(y,F)` as the sum of
  the fibre dimensions of `W^i` and `W^(i+1)` minus the constant rank of
  `L^(i+1)`.

## Sources

- [Hartshorne III.12, Theorem 12.8, p.288](../../../../sources/hartshorne-iii-11-12.md#semicontinuity-grauert-and-base-change-pp287291)
