---
article_id: af_1ef8d4d758eff98e0bb3e653
declaration: theorem
origin: cited
source_units: [chapter-v-section-5]
---

# The hyperplane-section genus defect decreases under blowup

Let `T:X dashedrightarrow X'` be a birational transformation of nonsingular
projective surfaces and let `H'` be very ample. Choose a smooth irreducible
curve `C'` in `|2H'|` avoiding the fundamental points of `T^(-1)`, and let
`C` be its image. Then

`m(T,H')=p_a(C)-p_a(C')`

is a nonnegative integer independent of the chosen admissible member `C'`.
If it is positive, blowing up a singular point of `C` strictly lowers it.
After finitely many point blowups `f:X''->X`, the transformed map
`T after f` has defect zero.

## Depends on

- [The fundamental locus on a normal surface is finite](../fundamental-loci/normal-source-fundamental-locus-codimension-two.md)
- [Simultaneous Bertini moving](../../intersection-theory/foundations/simultaneous-bertini-moving.md)
- [Bertini with finite-point avoidance](../../../schemes/differentials/canonical-bertini/bertini-avoid-finite-singular-set.md)
- [Irreducibility of regular Bertini sections](../../../cohomology/serre-duality/duality-applications/bertini-section-irreducible.md)
- [Arithmetic genus under normalization](../../../curves/riemann-roch/arithmetic-genus-normalization-formula.md)
- [Arithmetic-genus drop under point blowup](../../monoidal-transformations/strict-transforms/strict-transform-arithmetic-genus-drop.md)

## Proof depends on

- The restriction `C'->C` is finite and birational, so the normalization
  defect gives nonnegativity and characterizes zero. Images of linearly
  equivalent admissible members remain linearly equivalent, making `m`
  independent of the member. Every singular image point has multiplicity at
  least two, so its blowup strictly lowers arithmetic genus.

## Sources

- [Hartshorne V.5, proof of Theorem 5.5, pp.412–413](../../../../sources/hartshorne-v-5.md)
