---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-6-7]
---

# Determinant on the Grothendieck group of a curve

Let `X` be a nonsingular curve over an algebraically closed field. Every
coherent sheaf admits a length-one finite locally free resolution
`0 → E_1 → E_0 → F → 0`. Define

`det(F) = topExterior(E_0) tensor topExterior(E_1)^{-1}`

and prove independence of the resolution and additivity in short exact
sequences. Thus determinant induces `det : K(X) → Pic X`; for the divisor
class represented by a skyscraper sum, its determinant is `O_X(D)`.

This is exactly the determinant construction in Exercise 6.11(b); the other
parts of Exercise 6.11 are not targets.

## Depends on

- [The Grothendieck group of coherent sheaves](grothendieck-group-coherent-sheaves.md)
- [The Picard group of a ringed space](../cartier-picard/invertible-sheaf-group.md)
- [Finite twisted free covers](../../projective-sheaves/finite-twisted-free-cover.md)
- [Sheaf tensor, symmetric, and exterior operations](../../module-exercises/sheaf-tensor-operations.md)
- [The perfect exterior-power pairing](../../module-exercises/exterior-perfect-pairing.md)
- [Exterior powers of an exact sequence](../../module-exercises/exterior-power-exact-filtration.md)
- [Completion of a nonsingular curve](../../../projective-models/nonsingular-curve-projective-open.md)
- [Extension of coherent sheaves](../../coherent-sheaves/coherent-extension.md)

## Proof depends on

- Kernels of surjections from finite locally free sheaves are locally free on
  a nonsingular curve, by the DVR stalk criterion.
- Schanuel's lemma for independence of a resolution.

## Sources

- [Hartshorne II.6, Exercise 6.11(b) on printed p.149](../../../../sources/hartshorne-ii-6.md#adopted-exercises-and-later-use-evidence)
