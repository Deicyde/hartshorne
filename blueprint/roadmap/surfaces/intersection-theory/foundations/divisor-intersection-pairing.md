---
declaration: theorem
origin: cited
source_units: [chapter-v-section-1]
---

# The divisor intersection pairing

There is a unique pairing

`Div(X) times Div(X) -> Z`,  `(C,D) |-> C.D`,

which is symmetric, additive in each argument, invariant under linear
equivalence, and counts points for nonsingular curves meeting transversally.

The pairing is constructed directly by moving arbitrary divisors to
differences of very ample smooth curves; no Chow-group intersection product
is used.

## Depends on

- [Intersection of very ample divisors](very-ample-intersection-pairing.md)
- [Tensoring very ample with globally generated](../../../schemes/projective-geometry/linear-systems-ampleness/very-ample-tensor-globally-generated.md)
- [Ample invertible sheaves](../../../schemes/projective-geometry/linear-systems-ampleness/ample-invertible-sheaf.md)

## Proof depends on

- For a fixed ample `H` and arbitrary `C,D`, sufficiently large translates
  `C+nH`, `D+nH`, and `nH` are very ample.
- Expand differences bilinearly and use the cone pairing to prove independence
  of every chosen expression; the same expansion proves uniqueness.

## Sources

- [Hartshorne V.1, Theorem 1.1 and proof, pp.357–360](../../../../sources/hartshorne-v-1.md)
