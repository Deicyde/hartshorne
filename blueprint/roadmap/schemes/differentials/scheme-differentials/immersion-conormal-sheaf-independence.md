---
article_id: af_e270dcd9c883d0a770b48853
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.ConormalIndependence.ClosedFactorization.comparison Hartshorne.ConormalIndependence.ClosedFactorization.comparison_self Hartshorne.ConormalIndependence.ClosedFactorization.comparison_trans Hartshorne.ConormalIndependence.ClosedFactorization.toCanonical Hartshorne.ConormalIndependence.ClosedFactorization.comparison_toCanonical
---

# The conormal sheaf is independent of the closed neighbourhood

Let an immersion $i : Z \to X$ be factored through two open subschemes as closed
immersions. The two pullbacks of their ideal sheaves to $Z$ are canonically
isomorphic. These comparison isomorphisms are the identity for one
factorization and satisfy the cocycle law for three factorizations; hence they
identify either construction with the canonical conormal sheaf $N^*_i$.

## Depends on

- [The conormal sheaf of an immersion](immersion-conormal-sheaf.md)

## Proof depends on

- Compatibility of closed-immersion ideal sheaves and module pullback under
  restriction to a smaller open neighbourhood.
- Stacks Project, tags $01R1$–$01R3$.

## Sources

- [Hartshorne II.8, diagonal-conormal definition of differentials (pp. 175–176)](../../../../sources/hartshorne-ii-8.md#modules-and-sheaves-of-differentials)
- [Adopted Stacks sources for scheme differentials](../../../../sources/hartshorne-ii-8.md#external-proof-sources-and-unresolved-obligations)
