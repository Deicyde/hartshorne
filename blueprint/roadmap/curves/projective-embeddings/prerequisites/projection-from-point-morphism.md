---
article_id: af_250fea92495f2285d2e325da
declaration: theorem
origin: cited
lean: Hartshorne.projectionFromPoint_isProjection Hartshorne.projectionDomain Hartshorne.projectionFromPoint Hartshorne.existsUnique_projection Hartshorne.eq_projectionFromPoint_iff Hartshorne.isGeneratedBySections_projectionSections Hartshorne.projectivePoint Hartshorne.coordinatePoint Hartshorne.projectionDomain_eq_compl_range Hartshorne.hyperplaneInclusion Hartshorne.hyperplaneInclusion_notMem_projectiveSpaceChart_last Hartshorne.exists_lift_projectivePoint_comp_projectionFromPoint Hartshorne.exists_lift_projectivePoint_comp_projectionFromPoint_hyperplaneInclusion
---

# Projection from a point is a morphism

Let $H \simeq \mathbb{P}^n_k$ be a hyperplane in $\mathbb{P}^{n+1}_k$ and let $P$ be a point not
on $H$. For $Q \ne P$, let $\pi _P(Q)$ be the intersection with $H$ of the unique
line through $P$ and $Q$. Then

$\pi _P : \mathbb{P}^{n+1}_k \setminus \{P\} \to H$

is a morphism. After projective coordinates put $P$ at the omitted coordinate
point and $H$ at the corresponding coordinate hyperplane, it is the morphism
defined by the remaining homogeneous coordinates.

## Depends on

- [Projective space over a scheme](../../../schemes/proper-and-projective/projective-space-over-scheme.md)
- [Morphisms from generated invertible sheaves](../../../schemes/projective-geometry/linear-systems-ampleness/morphism-from-generated-line-bundle.md)
- [Coordinate nonvanishing opens](../../../schemes/projective-geometry/linear-systems-ampleness/coordinate-nonvanishing-open.md)

## Proof depends on

- The remaining coordinates have no common zero away from $P$ and define
  compatible morphisms on the standard affine charts.

## Sources

- [Hartshorne I.3, Exercise 3.14(a), p.22](../../../../sources/hartshorne.md#i3)
