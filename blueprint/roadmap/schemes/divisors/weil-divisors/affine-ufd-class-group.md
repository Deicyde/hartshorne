---
article_id: af_c4d1f0593a727c972632e4f6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.uniqueFactorizationMonoid_iff_isNormal_spec_and_weilClassGroup_subsingleton
---

# The affine UFD class-group criterion

For a Noetherian domain $A$, prove that $A$ is a unique factorization domain
if and only if $\operatorname{Spec} A$ is normal and $Cl(\operatorname{Spec} A)$ is trivial.
The class group is defined because a normal Noetherian integral separated
scheme satisfies condition $(*)$: its codimension-one local rings are
one-dimensional integrally closed Noetherian local domains, hence regular.

In the reverse direction, a height-one prime has divisor class zero; the
height-one intersection theorem turns its rational generator into an element
of $A$ and proves that the prime ideal is principal.

## Depends on

- [Linear equivalence and the Weil class group](weil-linear-equivalence.md)
- [Intersection of height-one localizations](height-one-localization-intersection.md)
- [Normal schemes](../../normalization-and-exercises/normal-scheme.md)

## Proof depends on

- In a unique factorization domain, every height-one prime ideal is principal.
- A UFD is integrally closed.

## Sources

- [Hartshorne II.6, Proposition 6.2 on printed pp.131–132](../../../../sources/hartshorne-ii-6.md#weil-divisors-and-class-groups)
