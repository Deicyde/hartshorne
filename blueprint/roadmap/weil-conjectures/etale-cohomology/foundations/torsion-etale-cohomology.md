---
declaration: def
origin: cited
source_units: [appendix-c-section-3]
---

# Torsion étale cohomology

For the constant étale sheaf `Z/ell^r Z`, define

`H^i_et(X,Z/ell^r Z)`

as the `i`th right-derived functor of global sections in the abelian category
of abelian sheaves on the small étale site.  Morphisms of schemes act by the
site-theoretic inverse-image construction.

## Depends on

- [Constant torsion sheaves](constant-torsion-etale-sheaf.md)
- [Right derived functors](../../../cohomology/derived-functors/right-derived-functors.md)

## Proof depends on

- The generic sheaf-cohomology infrastructure in
  `Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`; the coefficient
  sheaf and inverse-image functor must be instantiated on the small étale
  site.

## Sources

- [Hartshorne Appendix C §3, definition of ℓ-adic cohomology, p.453](../../../../sources/hartshorne-appendix-c-3.md#definition-and-coefficients-printed-p453)
- SGA 4.
