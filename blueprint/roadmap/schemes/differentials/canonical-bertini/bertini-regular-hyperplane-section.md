---
article_id: af_0f5b64d10c5dd8ceb550ec55
declaration: theorem
origin: cited
lean: Hartshorne.BertiniIncidence.bertini_regular_hyperplane_section
statement: formalized
proof: formalized
---

# Regular hyperplane sections

Let $X$ be a nonsingular closed subvariety of $\mathbb{P}^n_k$, with $k$ algebraically
closed. The hyperplanes $H$ not containing $X$ for which the scheme
$H \cap X$ is regular at every point form an open dense subset of the
complete linear system of hyperplanes.

By Remark III.7.9.1 (p.245), if $\dim X \ge 2$ then $H \cap X$ is also connected,
hence irreducible, so it is a nonsingular variety.

## Depends on

- [Linear systems](../../projective-geometry/linear-systems-ampleness/linear-system-api.md)
- [Regular points and nonsingular schemes](../scheme-differentials/regular-points-and-nonsingular-schemes.md)

## Proof depends on

- [The bad-hyperplane incidence correspondence](bertini-bad-hyperplane-incidence.md)
- [Images of proper schemes](../../proper-and-projective/proper-image.md)
- [Projective space is proper](../../proper-and-projective/projective-space-proper.md)
- $p_2(B)$ has dimension at most $\dim B = n - 1 < n = \dim |H|$, so it is a
  proper closed subset of the irreducible $|H|$, and its complement is open and
  dense.

## Sources

- [Hartshorne II.8, Theorem 8.18 (pp.179–180)](../../../../sources/hartshorne-ii-8.md#nonsingular-varieties-and-bertini)
- [Stacks Project, Bertini theorems, tag 0FD4](../../../../sources/hartshorne-ii-8.md#external-proof-sources-and-unresolved-obligations)
