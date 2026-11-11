---
article_id: af_dafd958e44d3a633b1b25e55
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.CanonicalSectionRing Hartshorne.CanonicalSectionRing.gRing Hartshorne.canonicalSectionRingCommRing Hartshorne.canonicalSectionRing_degreeZero_bijective Hartshorne.DivisorMultipleSectionRing Hartshorne.canonicalSectionRingEquivOfDivisor Hartshorne.canonicalSectionRingEquivOfDivisor_of Hartshorne.DivisorMultipleSectionRing.of_mul_of Hartshorne.DivisorMultipleSectionRing.one_eq
---

# The canonical section ring

Let $X$ be a nonsingular projective integral variety over an algebraically
closed field, with canonical invertible sheaf $\omega_X$. Define the graded
canonical section ring

$R(X,K)=\bigoplus_{n\ge0}H^0(X,\omega_X^{\otimes n})$,

with degree-zero term $k$ and multiplication induced by tensor product of
sections. The equality in degree zero uses $H^0(X,\mathcal{O}_X)=k$. Defining the ring
through $\omega_X$ avoids choosing a canonical divisor. If a canonical divisor
$K$ is used instead, a chosen isomorphism $\mathcal{O}_X(K)\cong\omega_X$ induces a
graded-ring isomorphism
$\bigoplus_{n\ge0}H^0(X,\mathcal{O}_X(nK))\cong R(X,K)$.

## Depends on

- [The canonical sheaf](../../../schemes/differentials/canonical-bertini/canonical-sheaf.md)
- [The canonical divisor class](../../../schemes/differentials/canonical-bertini/canonical-divisor-class.md)
- [Sheaf tensor, symmetric, and exterior operations](../../../schemes/module-exercises/sheaf-tensor-operations.md)

## Proof depends on

- [The global regular functions of a projective variety](../../../morphisms/projective-rings/projective-global-regular.md)

## Sources

- [Hartshorne V.6, canonical-ring definition, p.421](../../../../sources/hartshorne-v-6.md)
