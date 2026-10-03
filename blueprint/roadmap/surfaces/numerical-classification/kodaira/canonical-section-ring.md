---
declaration: def
origin: cited
source_units: [chapter-v-section-6]
---

# The canonical section ring

Let `X` be a nonsingular projective integral variety over an algebraically
closed field, with canonical invertible sheaf `omega_X`. Define the graded
canonical section ring

`R(X,K)=direct-sum_(n>=0) H^0(X,omega_X tensor-power n)`,

with degree-zero term `k` and multiplication induced by tensor product of
sections. The equality in degree zero uses `H^0(X,O_X)=k`. Defining the ring
through `omega_X` avoids choosing a canonical divisor. If divisor
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
