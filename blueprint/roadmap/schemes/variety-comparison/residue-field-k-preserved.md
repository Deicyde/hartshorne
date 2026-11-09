---
article_id: af_865d81387d6d127ca796c78f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.bijective_residueFieldStructureMap_map Hartshorne.residueFieldStructureMap
---

# Morphisms over $k$ preserve points with residue field $k$

Let $k$ be a field and let $f : X \to Y$ be a morphism of schemes over $k$.  A
point $P \in X$ has residue field $k$ when the map $k \to \kappa(P)$ induced by the
structure morphism $X \to \operatorname{Spec} k$ is an isomorphism.  If $P \in X$ has
residue field $k$, then $f(P) \in Y$ also has residue field $k$.

In Hartshorne's Exercise II.2.15(b), $k$ is the algebraically closed field of
part (a); the argument uses no hypothesis on $k$.

The local homomorphism $\mathcal{O}_{Y,f(P)} \to \mathcal{O}_{X,P}$ induces a field
homomorphism $\kappa(f(P)) \to \kappa(P)$, and it is a homomorphism of $k$-algebras
because $f$ commutes with the structure morphisms.  The composite
$k \to \kappa(f(P)) \to \kappa(P)$ is the isomorphism $k \to \kappa(P)$.  The field
homomorphism $\kappa(f(P)) \to \kappa(P)$ is injective, and it is surjective because
the composite is; so it is an isomorphism, and therefore so is
$k \to \kappa(f(P))$.

## Depends on

- [Schemes over a base](../spectrum-and-schemes/over-base.md)
- [Locally ringed spaces](../spectrum-and-schemes/locally-ringed-space.md)

## Sources

- [Hartshorne II.2, Exercise 2.15(b) (p. 81)](../../../sources/hartshorne-ii-2.md#exercises-212-through-219)
