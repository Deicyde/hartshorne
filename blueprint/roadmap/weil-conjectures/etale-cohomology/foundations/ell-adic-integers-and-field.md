---
article_id: af_e3cca5b53e68a242841d754a
declaration: structure
origin: bridged
source_units: [appendix-c-section-3]
---

# The ℓ-adic integers and coefficient field

For a prime `ell`, identify

`Z_ell = inverse-limit_r Z/ell^r Z`

with Mathlib's `PadicInt ell`, notation `Z_[ell]`, and let

`Q_ell = Frac(Z_ell)`

be Mathlib's `Padic ell`, notation `Q_[ell]`.  Record the reduction maps to
`ZMod (ell^r)` and the scalar extension `Z_ell -> Q_ell`.

This coefficient package is existing infrastructure, but no single pinned
declaration states the whole inverse-limit/fraction-field bridge as this
source-shaped leaf.

## Depends on

No project-local geometric prerequisite; this leaf packages pinned p-adic
coefficient-ring infrastructure in the source's inverse-system convention.

## Proof depends on

- `PadicInt`, `Padic`, `PadicInt.toZModPow`, and the universal-property
  declarations in `Mathlib/NumberTheory/Padics/RingHoms.lean`.
- Categorical inverse limits of the reduction system `ZMod (ell^r)`.

## Sources

- [Hartshorne Appendix C §3, ℓ-adic coefficient rings, p.453](../../../../sources/hartshorne-appendix-c-3.md#definition-and-coefficients-printed-p453)
