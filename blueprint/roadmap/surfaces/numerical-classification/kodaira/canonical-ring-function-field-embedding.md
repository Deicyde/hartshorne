---
declaration: theorem
origin: bridged
source_units: [chapter-v-section-6]
---

# Section rings embed in a polynomial ring over the function field

Let `X` be a nonsingular projective integral `d`-fold and `L` an invertible
sheaf. A rational trivialization of `L` sends a degree-`n` section to
`f*t^n` and defines an injective graded algebra map

`direct-sum_(n>=0) H^0(X,L^n) -> K(X)[t]`.

Consequently every such section ring is a domain of finite transcendence
degree at most `d+1` over the ground field. Specializing to `L=omega_X` gives
the canonical-ring statement. Changing the rational trivialization conjugates
the embedding by a graded rescaling and does not change the transcendence
degree.

## Depends on

- [The canonical section ring](canonical-section-ring.md)
- [Locally free and invertible module sheaves](../../../schemes/modules-and-quasicoherent/locally-free-and-invertible.md)
- [The function field of an integral scheme](../../../schemes/normalization-and-exercises/function-field-integral-scheme.md)
- [Dimension of a scheme](../../../schemes/subschemes-and-dimension/scheme-dimension.md)
- [Dimension of a finitely generated domain](../../../affine-varieties/dim-fg-domain.md)

## Proof depends on

- A rational generator of the rank-one generic fibre of `L`; regular
  sections inject into rational sections on an integral scheme.
- `trdeg_k K(X)=d` and `trdeg_k K(X)(t)=d+1`.

## Sources

- [Hartshorne V.6, canonical-ring and Kodaira-dimension setup, pp.421–422](../../../../sources/hartshorne-v-6.md)
