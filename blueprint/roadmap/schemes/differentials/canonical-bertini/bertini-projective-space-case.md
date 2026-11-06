---
article_id: af_17f7dc9756447de8a8a05c90
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.nonempty_iso_hyperplaneSection Hartshorne.hyperplaneSection_isRegular Hartshorne.hyperplaneSection Hartshorne.hyperplaneSectionι Hartshorne.hyperplaneIdeal Hartshorne.projectiveSpaceScheme_isRegular
---

# The projective-space case of Bertini

For $n \ge 1$ and $X = \mathbb{P}^n_k$, every hyperplane section is a projective space
$\mathbb{P}^{n-1}_k$ and hence is regular. Thus the good set in the complete linear
system is all of $|H|$.

This separates the case $\dim X = n$, in which the source's expression
$\mathbb{P}^{n-r-1}$ would have dimension $-1$, from the incidence calculation for a
proper closed subvariety.

## Depends on

- [Projective space over a ring](../../projective-spectrum/projective-space-over-ring.md)
- [Regular points and nonsingular schemes](../scheme-differentials/regular-points-and-nonsingular-schemes.md)

## Proof depends on

- A hyperplane in projective space is isomorphic to lower-dimensional
  projective space.
- Polynomial rings over a field are regular.

## Sources

- [Hartshorne II.8, projective-space case in Theorem 8.18 (pp.179–180)](../../../../sources/hartshorne-ii-8.md#nonsingular-varieties-and-bertini)
