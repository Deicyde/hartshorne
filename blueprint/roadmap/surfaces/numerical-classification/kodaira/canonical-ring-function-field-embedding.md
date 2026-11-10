---
article_id: af_0f97d9366f82584efe3518bd
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.TensorPowerSectionRing.toPolynomialOfIso Hartshorne.TensorPowerSectionRing.toPolynomialOfIso_of Hartshorne.TensorPowerSectionRing.toPolynomialOfIso_injective Hartshorne.TensorPowerSectionRing.toPolynomialOfIsoAlgHom Hartshorne.TensorPowerSectionRing.exists_injective_toPolynomial Hartshorne.TensorPowerSectionRing.isDomain_of_isInvertible Hartshorne.TensorPowerSectionRing.trdeg_le Hartshorne.TensorPowerSectionRing.exists_toPolynomialOfIso_eq_aeval Hartshorne.canonicalSectionRing_exists_injective_toPolynomial Hartshorne.canonicalSectionRing_isDomain Hartshorne.canonicalSectionRing_trdeg_le
---

# Section rings embed in a polynomial ring over the function field

Let $X$ be a nonsingular projective integral $d$-fold and $L$ an invertible
sheaf. A rational trivialization of $L$ sends a degree-$n$ section to
$f\cdot t^n$ and defines an injective graded algebra map

$\bigoplus_{n\ge0}H^0(X,L^n)\longrightarrow K(X)[t]$.

Consequently every such section ring is a domain of finite transcendence
degree at most $d+1$ over the ground field. Specializing to $L=\omega _X$ gives
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

- A rational generator of the rank-one generic fibre of $L$; regular
  sections inject into rational sections on an integral scheme.
- $\operatorname{trdeg} _k K(X)=d$ and $\operatorname{trdeg} _k K(X)(t)=d+1$.

## Sources

- [Hartshorne V.6, canonical-ring and Kodaira-dimension setup, pp.421–422](../../../../sources/hartshorne-v-6.md)
