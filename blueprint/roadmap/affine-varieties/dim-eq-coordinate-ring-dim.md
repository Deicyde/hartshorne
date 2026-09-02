---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.dim_eq_ringKrullDim_coordinateRing Hartshorne.irreducibleClosedsOrderIso Hartshorne.subtypeIrreducibleClosedsOrderIso
---

# Dimension is the dimension of the coordinate ring

For an affine algebraic set `Y`, the dimension of `Y` as a topological space
equals the Krull dimension of `A(Y)` (Proposition 1.7).

The proof is a chain of order isomorphisms rather than a computation: closed
irreducible subsets of `Y` correspond to primes of `A` containing `I(Y)`, which
correspond to primes of `A(Y)`. Both correspondences reverse inclusion, so
chains of length `n` match chains of length `n`, and the suprema agree.

This is the bridge that lets every dimension statement about varieties be
answered by commutative algebra, and every later dimension result in the chapter
routes through it. In Lean the cleanest route is likely an order isomorphism
between `IrreducibleCloseds Y` and `PrimeSpectrum (A(Y))`, after which
`topologicalKrullDim` and `ringKrullDim` agree by transport.

## Depends on

- [Dimension of a topological space and of a ring](dimension.md)
- [The affine coordinate ring](affine-coordinate-ring.md)

## Proof depends on

- [Algebraic sets and radical ideals](radical-ideal-correspondence.md)

## Sources

- [Hartshorne I.1, Proposition 1.7 (p. 6)](../../sources/hartshorne.md#i1)
