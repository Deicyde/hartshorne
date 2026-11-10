---
article_id: af_dafd958e44d3a633b1b25e55
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.CanonicalSectionRing Hartshorne.CanonicalSectionRing.Component Hartshorne.CanonicalSectionRing.gRing Hartshorne.canonicalSectionRingCommRing Hartshorne.canonicalSectionRing_degreeZero_bijective Hartshorne.TensorPowerSectionRing.gRing Hartshorne.TensorPowerSectionRing.commRing Hartshorne.TensorPowerSectionRing.ι_mul_comm Hartshorne.TensorPowerSectionRing.smul_oneSec_bijective Hartshorne.canonicalSectionRingEquivOfDivisor Hartshorne.canonicalSectionRingEquivOfDivisor_of Hartshorne.DivisorMultipleSectionRing Hartshorne.canonicalDivisorPowIso AlgebraicGeometry.Scheme.CartierDivisor.nsmulSheafIso Hartshorne.TensorPowerSectionRing.ringEquiv Hartshorne.TensorPowerSectionRing.powMap_mul
---

# The canonical section ring

Let $X$ be a nonsingular projective integral variety over an algebraically
closed field, with canonical invertible sheaf $\omega _X$. Define the graded
canonical section ring

$R(X,K)=\bigoplus_{n\ge0}H^0(X,\omega_X^{\otimes n})$,

with degree-zero term $k$ and multiplication induced by tensor product of
sections. The equality in degree zero uses $H^0(X,\mathcal{O}_X)=k$. Defining the ring
through $\omega _X$ avoids choosing a canonical divisor. If divisor
representatives are used, a chosen linear equivalence induces a graded-ring
isomorphism; there is no choice-free canonical isomorphism of those
presentations.

## Depends on

- [The canonical sheaf](../../../schemes/differentials/canonical-bertini/canonical-sheaf.md)
- [The canonical divisor class](../../../schemes/differentials/canonical-bertini/canonical-divisor-class.md)
- [Sheaf tensor, symmetric, and exterior operations](../../../schemes/module-exercises/sheaf-tensor-operations.md)
- [The global regular functions of a projective variety](../../../morphisms/projective-rings/projective-global-regular.md)

## Sources

- [Hartshorne V.6, canonical-ring definition, p.421](../../../../sources/hartshorne-v-6.md)
