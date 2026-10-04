---
article_id: af_ca7f077876a7f2d58fc6288d
declaration: theorem
origin: cited
source_units: [chapter-v-section-6]
not_ready: true
---

# Abelian and hyperelliptic surface data

For a two-dimensional abelian variety `A` over an algebraically closed field
of arbitrary characteristic, translation-invariant differentials give

`K_A~0`, `q(A)=2`, `p_g(A)=1`, and `p_a(A)=-1`.

If in addition `char k != 2,3`, then for a hyperelliptic surface in the
classical quotient interface, projection to the factor quotient
`F/G~=P^1` descends to a morphism whose fibres over a dense open subset are
nonsingular genus-one curves.  Thus it has the elliptic pencil asserted by
Hartshorne.  These two surface types remain distinct: the hyperelliptic
surface is not being given the structure of an abelian variety.

This node is not ready until exact sources and APIs are adopted for
structure-sheaf cohomology of abelian surfaces and for finite free quotients
and descent of the hyperelliptic fibration.

## Depends on

- [The four surface-type interfaces](surface-type-definition-api.md)
- [The irregularity formula](../../../cohomology/serre-duality/duality-applications/smooth-surface-irregularity-formula.md)
- [Elliptic-surface fibrations](../kappa-one/elliptic-surface-fibration.md)

## Proof depends on

- The cotangent bundle of an abelian variety is trivialized by invariant
  one-forms, and its structure-sheaf cohomology is the exterior algebra on
  `H^1(A,O_A)`.
- Freeness of the finite quotient action permits descent of the projection;
  away from the finitely many nonfree fibres on the second factor, its fibres
  are elliptic curves.

## Sources

- [Hartshorne V.6, abelian and hyperelliptic clauses of Theorem 6.3, p.422](../../../../sources/hartshorne-v-6.md)
- Bombieri–Husemoller and Shafarevich for the quotient model.
