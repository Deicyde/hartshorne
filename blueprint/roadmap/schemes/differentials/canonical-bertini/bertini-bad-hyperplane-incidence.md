---
article_id: af_b0aec91c31bd340fb59fa8fb
declaration: theorem
origin: cited
lean: Hartshorne.BertiniIncidence.bertini_bad_hyperplane_incidence Hartshorne.BertiniIncidence.badHyperplaneSubspace Hartshorne.BertiniIncidence.IsBadHyperplaneAt Hartshorne.BertiniIncidence.hyperplaneSectionIdeal Hartshorne.BertiniIncidence.incidenceAmbient Hartshorne.BertiniIncidence.dualProjectiveSpaceStructure Hartshorne.BertiniIncidence.Represents
statement: formalized
proof: formalized
---

# The bad-hyperplane incidence correspondence

Let $X \subseteq \mathbb{P}^n_k$ be a nonsingular closed subvariety of dimension
$r < n$, with $k$ algebraically closed. For each closed point $x \in X$, the
hyperplanes that contain $X$, or whose section with $X$ is not regular at $x$,
form a projective linear subspace $B_x$ of dimension $n - r - 1$. The pairs
$(x, H)$ with $x \in X$ closed and $H \in B_x$ are the closed points of a closed
irreducible subset $B \subseteq X \times |H|$ of dimension $n - 1$. (For $r = n$
each $B_x$ is empty.)

## Depends on

- [Linear systems](../../projective-geometry/linear-systems-ampleness/linear-system-api.md)
- [Dimension of a projective variety](../../../projective-varieties/projective-dimension.md)

## Proof depends on

- [Regular hypersurface quotients of a regular local ring](regular-hypersurface-local-criterion.md)
- [Separation of points and tangent vectors](../../projective-geometry/linear-systems-ampleness/separates-points-tangents-iff-closed-immersion.md)
- The projective bundle associated to the kernels of the pointwise first-jet
  evaluation maps.

## Sources

- [Hartshorne II.8, proof of Theorem 8.18 (pp.179–180)](../../../../sources/hartshorne-ii-8.md#nonsingular-varieties-and-bertini)
