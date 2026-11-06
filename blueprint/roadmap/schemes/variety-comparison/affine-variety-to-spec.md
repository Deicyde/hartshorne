---
article_id: af_6a2e5ff2057aec8d2fb1fb78
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.affineVarietyGenericCompletionIsoSpec Hartshorne.affineVarietyGenericCompletionLocallyRingedSpace Hartshorne.affineVarietyGenericCompletionSheafedSpaceIsoSpec Hartshorne.genericCompletionHomeomorphSpec Hartshorne.affineVarietyGenericCompletionIsoSpec_hom_base_asIdeal Hartshorne.affineVarietyGenericCompletionIsoSpec_hom_base_alpha Hartshorne.affineVarietyGenericCompletionIsoSpec_hom_c_app
---

# An affine variety completes to its spectrum

Let $V$ be an affine variety over an algebraically closed field $k$, with
coordinate ring $A(V)$.  There is a canonical isomorphism of locally ringed
spaces

$(t(V), \alpha _{V\cdot }\mathcal{O} _V) \cong \operatorname{Spec} A(V)$.

On points, send an irreducible closed subset to its prime vanishing ideal; the
Chapter I radical-ideal correspondence supplies the inverse and proves the
homeomorphism.  Here the Nullstellensatz enters as the statement that a prime
of $A(V)$ is the intersection of the maximal ideals $\mathfrak{m}_P$ containing it,
and a point $P$ of $V$ goes to $\mathfrak{m}_P$.

On opens, identify regular functions with the locally fractional
structure-sheaf sections: a section goes to the function whose value at $P$ is
its germ in $A(V)_{\mathfrak{m}_P}$ evaluated at $P$.  Locally the section is
$a/f$, so the function is locally $a(P)/f(P)$ and is regular.  Injectivity
and surjectivity both rest on the identity principle in $A(V) \subseteq \mathcal{O} (V)$:
an element vanishing on a nonempty open subset of $V$ is zero.  For
surjectivity, write a regular function as $a/f$ near a point of the zero set
of each prime; any two such quotients agree on a nonempty open set, hence in
every localization, and they glue to a section.

## Depends on

- [The regular-function sheaf on the generic completion](generic-completion-sheaf.md)
- [The structure sheaf on Spec](../spectrum-and-schemes/spec-structure-sheaf.md)
- [Radical ideal correspondence](../../affine-varieties/radical-ideal-correspondence.md)

## Proof depends on

- [Coordinate ring is the ring of regular functions](../../morphisms/global-regular-eq-coordinate-ring.md)
- [The local ring is a localisation](../../morphisms/local-ring-is-localization.md)

## Sources

- [Hartshorne II.2, affine case of Proposition 2.6 (p. 78)](../../../sources/hartshorne-ii-2.md#schemes-over-a-base-and-proposition-26)
