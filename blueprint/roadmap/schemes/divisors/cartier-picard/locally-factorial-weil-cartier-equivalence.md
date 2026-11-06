---
article_id: af_80f6d4cc27ebb567666021b8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.cartierToWeil AlgebraicGeometry.Scheme.cartierToWeil_apply AlgebraicGeometry.Scheme.weilCartierEquiv AlgebraicGeometry.Scheme.weilCartierEquiv_symm_apply AlgebraicGeometry.Scheme.weilCartierEquiv_principalDivisor AlgebraicGeometry.Scheme.map_principalDivisorSubgroup_weilCartierEquiv AlgebraicGeometry.Scheme.isLocallyPrincipal_of_isLocallyFactorial AlgebraicGeometry.Scheme.cartierEquivLocallyPrincipal AlgebraicGeometry.Scheme.coe_cartierEquivLocallyPrincipal AlgebraicGeometry.Scheme.mem_locallyPrincipalWeilDivisors
---

# Weil and Cartier divisors on locally factorial schemes

Let $X$ be integral, separated, Noetherian, and locally factorial. Construct
mutually inverse additive equivalences between the Weil divisor group and the
Cartier divisor group, and prove that principal divisors correspond.

For a normal integral Noetherian scheme, prove as a supporting refinement that
the same construction identifies Cartier divisors with the subgroup of
locally principal Weil divisors. The locally factorial hypothesis makes every
Weil divisor locally principal.

In the refinement the scheme is also taken to be separated, as in condition
$(*)$, under which Weil divisors and principal divisors are considered.

## Depends on

- [Principal divisors have finite support](../weil-divisors/principal-divisor-finite-support.md)
- [Intersection of height-one localizations](../weil-divisors/height-one-localization-intersection.md)
- [Principal Cartier divisors and the Cartier class group](cartier-class-group.md)
- [Locally factorial schemes](locally-factorial-schemes.md)

## Proof depends on

- Height-one prime ideals in a UFD are principal.
- On a normal affine open, two rational functions with the same height-one
  orders differ by a regular unit.

## Sources

- [Hartshorne II.6, Proposition 6.11 and Remark 6.11.2 on printed pp.141–142](../../../../sources/hartshorne-ii-6.md#cartier-divisors-and-invertible-sheaves)
