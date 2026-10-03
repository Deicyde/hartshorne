---
declaration: short exact sequence
origin: cited
source_units: [chapter-iii-sections-6-7]
---

# The differential principal-parts resolution

For a complete nonsingular curve `X` over an algebraically closed field `k`,
with function field `K`, let `Ω_K` denote the constant sheaf with value
`Ω_(K/k)`. There is a flasque resolution

`0 ⟶ Ω_X ⟶ Ω_K ⟶ ⊕_(P∈X_closed) i_(P,*)(Ω_(K/k)/Ω_(X,P)) ⟶ 0`.

Consequently `H¹(X,Ω_X)` is the cokernel of the rational-differential
principal-parts map. Unlike the special `P¹` resolution, no surjectivity on
global sections before taking this cokernel is asserted.

## Depends on

- [The constant sheaf](../../../schemes/sheaves/constant-sheaf.md)
- [Skyscraper and closed extension by zero](../../../schemes/sheaf-functors/closed-extension-by-zero.md)
- [The canonical sheaf](../../../schemes/differentials/canonical-bertini/canonical-sheaf.md)
- [The function field of a projective variety](../../../morphisms/projective-rings/projective-function-field.md)

## Proof depends on

- [Exactness is detected on stalks](../../../schemes/sheaves/stalkwise-exactness.md)
- [Flasque sheaves are acyclic](../../sheaf-cohomology/flasque-sheaf-acyclic.md)
- Local freeness of `Ω_X` of rank one.
- The general curve principal-parts decomposition over closed points, proved
  stalkwise rather than imported from the special `P¹` case.

## Sources

- [Hartshorne III.7, differential principal-parts resolution, p.248](../../../../sources/hartshorne-iii-7.md#residues-on-curves-pp247248)
