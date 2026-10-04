---
article_id: af_6996e552979983497d8c0cea
declaration: def
origin: cited
source_units: [appendix-c-section-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.Scheme.smallEtaleTopology
mathlib_file: Mathlib/AlgebraicGeometry/Sites/Etale.lean
---

# The small étale site of a scheme

For a scheme `X`, the small étale site has schemes étale over `X` as objects
and jointly surjective families of étale `X`-morphisms as covering families.
The associated Grothendieck topology is
`AlgebraicGeometry.Scheme.smallEtaleTopology X`.

The pinned library also supplies `smallEtalePretopology` and identifies an
arrow-family cover by
`ofArrows_mem_smallEtaleTopology_iff`.  This is the small site, not the big
étale or pro-étale site.

## Depends on

- [Étale morphisms](../../../cohomology/smooth-morphisms/criteria/etale-flat-unramified-equivalences.md)

## Sources

- [Hartshorne Appendix C §3, étale-topology setup, p.453](../../../../sources/hartshorne-appendix-c-3.md#definition-and-coefficients-printed-p453)
- SGA 4, étale topology.
