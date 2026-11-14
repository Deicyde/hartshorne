---
article_id: af_81dbc7a4e0db6808ddcfb8a4
declaration: def
origin: bridged
lean: Hartshorne.existsUnique_linearSystemMorphism Hartshorne.linearSystemMorphism Hartshorne.linearSystemMorphism_spec Hartshorne.comap_invertibleZeroIdeal_linearSystemSection Hartshorne.isLocallyPrincipalNonZeroDivisor_invertibleZeroIdeal Hartshorne.exists_isEffective_idealSheafData_eq_invertibleZeroIdeal Hartshorne.linearSystemMorphism_map
statement: formalized
proof: formalized
---

# Finite-dimensional linear systems on an arbitrary variety

Let $X$ be an integral finite-type scheme over a field, $L$ an invertible
sheaf, and $V$ a finite-dimensional subspace of $\Gamma (X,L)$. Construct its
scheme-theoretic base locus. On the complement, the evaluation map is
surjective and defines a morphism to the projective space $P(V)$ such that the
zero scheme of every nonzero section in $V$ is the pullback of its parameter
hyperplane.

If $X$ is nonsingular, each nonzero section defines an effective
Cartier zero scheme away from components on which it vanishes
identically. No projectivity hypothesis on $X$ is required.
The integrality, finite-type and nonsingularity hypotheses are kept as in the source; the base
locus, the morphism and the hyperplane assertion hold for every scheme over the field, and on any
integral $X$, nonsingular or not, every nonzero section has an effective Cartier zero scheme.
This is the setting used in Hartshorne's Remark III.10.9.2.

## Depends on

- [Locally free module sheaves](../../schemes/modules-and-quasicoherent/locally-free-and-invertible.md)
- [Effective Cartier divisors as closed subschemes](../../schemes/divisors/cartier-picard/effective-cartier-closed-subscheme.md)
- [Projective space over a scheme](../../schemes/proper-and-projective/projective-space-over-scheme.md)
- [Morphisms from generated invertible sheaves](../../schemes/projective-geometry/linear-systems-ampleness/morphism-from-generated-line-bundle.md)
- [The zero scheme of a section of a locally free sheaf](../../intersection-theory/chern-classes/section-zero-scheme.md)
- [Clearing denominators with an invertible section](../../schemes/projective-sheaves/invertible-section-clearing-denominators.md)
- [Linear systems](../../schemes/projective-geometry/linear-systems-ampleness/linear-system-api.md)

## Proof depends on

- [Rees algebras and blowups](../../schemes/projective-geometry/blowups/rees-algebra-sheaf-and-blowup.md)

## Sources

- [Hartshorne III.10, Corollary 10.9 and Remark 10.9.2, pp.274–275](../../../sources/hartshorne-iii-10.md#homogeneous-spaces-kleiman-and-bertini-pp272275)
