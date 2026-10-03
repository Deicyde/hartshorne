---
declaration: isomorphism
origin: cited
source_units: [chapter-iii-sections-1-4]
not_ready: true
---

# First cohomology as the refinement colimit

For every topological space `X`, choose a small refinement category whose
objects are indexed open covers and whose morphisms are refinement functions
with their containment proofs. For every abelian sheaf `F`, the induced maps
on first Čech cohomology define a diagram, and the natural comparison is an
isomorphism

`colim_U CechH^1(U,F) ≅ H^1(X,F)`.

## Depends on

- [Comparison from Čech to sheaf cohomology](../cech-cohomology/cech-derived-comparison.md)

## Proof depends on

- [Flasque sheaves are Čech-acyclic](../cech-cohomology/flasque-cech-acyclic.md)
- Construct refinement maps and prove independence of the chosen refinement
  function after passage to a common refinement; parallel refinement
  functions must induce the same map in `H^1` after further refinement.
- Prove that the chosen small category is filtered, or exhibit a small
  cofinal replacement of the large category of all indexed covers.
- Embed `F` in a flasque sheaf and compare cokernel complexes.

## Sources

- [Hartshorne III, Exercise 4.4 (p.223)](../../../sources/hartshorne-iii-3-4.md#adopted-exercises-and-later-use)
- [External proof obligations](../../../sources/hartshorne-iii-3-4.md#external-proof-obligations)
