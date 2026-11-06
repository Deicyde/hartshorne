---
article_id: af_b7ae0b84eda54002bfe67819
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.Modules.bijective_presheaf_map_top_of_two_le_codim
---

# Locally free sections extend across codimension two

Let $X$ be a normal integral Noetherian scheme, let $U \subset X$ be an open
subscheme whose complement has codimension at least two, and let $E$ be a
finite locally free sheaf on $X$. Restriction is an isomorphism

$\Gamma (X, E) \simeq \Gamma (U, E|_U)$.

Since $X$ is integral, hence connected, a finite locally free sheaf on $X$ is locally
isomorphic to $\mathcal{O}_X^{r}$ for one fixed integer $r \ge 0$.

## Depends on

- [Normal schemes](../../normalization-and-exercises/normal-scheme.md)
- [Intersection of height-one localizations](../../divisors/weil-divisors/height-one-localization-intersection.md)
- [Locally free and invertible module sheaves](../../modules-and-quasicoherent/locally-free-and-invertible.md)
- [Codimension in a scheme](../../subschemes-and-dimension/scheme-codimension.md)

## Proof depends on

- Trivialize $E$ on affine opens and apply the height-one intersection theorem
  componentwise.
- Uniqueness on overlaps follows from density.

## Sources

- [Hartshorne II.8, section-extension step in the proof of Theorem 8.19 (pp.181–182)](../../../../sources/hartshorne-ii-8.md#canonical-sheaves-and-adjunction)
- [Hartshorne II.8, the same method requested for Exercise 8.8 (p.190)](../../../../sources/hartshorne-ii-8.md#adopted-exercises-and-later-use-evidence)
