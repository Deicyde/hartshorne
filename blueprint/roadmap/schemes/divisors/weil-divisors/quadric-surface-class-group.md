---
article_id: af_f40ca5db49f3d45395b96926
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.quadricClassGroupPullbackEquiv Hartshorne.quadricClassGroupPullbackEquiv_apply Hartshorne.quadricClassGroupPullbackOne Hartshorne.quadricClassGroupPullbackTwo Hartshorne.quadricProjOne Hartshorne.quadricProjTwo Hartshorne.quadricSurfaceClassGroupEquiv Hartshorne.quadricSurfaceClassGroupEquiv_pullback_add Hartshorne.quadricSurfaceClassGroupEquiv_rulingOne Hartshorne.quadricSurfaceClassGroupEquiv_rulingTwo Hartshorne.quadricSurfaceClassGroupEquiv_hyperplaneSection Hartshorne.quadricSurfaceClassGroupEquiv_lineOne Hartshorne.quadricSurfaceClassGroupEquiv_lineTwo Hartshorne.quadricAmbientClassGroupHom Hartshorne.quadricAmbientClassGroupHom_weilDivisorClassHom Hartshorne.exists_weilDivisorClassHom_eq_of_quadric Hartshorne.quadricSurfaceClassGroupEquiv_quadricAmbientClassGroupHom_hyperplane
---

# The class group of a nonsingular quadric surface

Let $Q \subseteq \mathbb{P}^3_k$ be the split nonsingular quadric $xy = zw$, identified with
$\mathbb{P}^1_k \times \mathbb{P}^1_k$. Prove that pullback from the two factors gives
$\operatorname{Cl} Q \cong \mathbb{Z} \times \mathbb{Z}$, and that a line of either ruling (the fibre over a
$k$-point) has class $(1,0)$ or $(0,1)$.

Prove that the embedding $Q \subseteq \mathbb{P}^3_k$ induces a homomorphism
$\operatorname{Cl} \mathbb{P}^3_k \to \operatorname{Cl} Q$: it sends the class of a divisor $D$ on $\mathbb{P}^3_k$,
none of whose components contains $Q$, to the class of the divisor $D \cdot Q$
cut on $Q$, and every class of $\operatorname{Cl} \mathbb{P}^3_k$ is the class of such a divisor.
The image of the class of a hyperplane $H$, which generates
$\operatorname{Cl} \mathbb{P}^3_k$, is $(1,1)$.

The ruling and hyperplane formulas normalize the isomorphism and are used by
later linear-system, curve, and surface calculations.

## Depends on

- [The split quadric surface is $\mathbb{P}^1 \times \mathbb{P}^1$](split-quadric-product-of-lines.md)
- [Restriction of class groups to open complements](class-group-open-restriction.md)
- [Affine-line invariance of the class group](a1-class-group-invariance.md)
- [The class group of projective space](projective-space-class-group.md)
- [Ambient hypersurfaces cut divisors](../divisor-exercises/projective-intersection-divisor.md)
- [Pullback on Picard groups](../divisor-exercises/picard-pullback.md)
- [Weil classes and the Picard group on a locally factorial scheme](../cartier-picard/locally-factorial-class-picard-equivalence.md)
- [Regular schemes are locally factorial](../cartier-picard/regular-locally-factorial.md)

## Proof depends on

- [Divisors of homogeneous fractions on Proj of a graded domain](proj-homogeneous-fraction-order.md)
- [Intersection of height-one localizations](height-one-localization-intersection.md)
- [The affine UFD class-group criterion](affine-ufd-class-group.md)
- The hyperplane section $w = 0$ is the sum of one line from each ruling.
- A hypersurface of degree $d$ not containing $Q$ cuts on $Q$ a divisor linearly equivalent to
  $d$ times a hyperplane section.

## Sources

- [Hartshorne II.6, Examples 6.6.1–6.6.2 on printed pp.135–136](../../../../sources/hartshorne-ii-6.md#weil-divisors-and-class-groups)
