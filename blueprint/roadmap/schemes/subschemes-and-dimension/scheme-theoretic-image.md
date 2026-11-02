---
article_id: af_aaa59dc38407697cafd8a7df
declaration: def
origin: cited
mathlib: true
mathlib_declaration: AlgebraicGeometry.Scheme.kerAdjunction
mathlib_file: Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean
---

# The scheme-theoretic image

For every morphism $f:Z\to X$, there is a closed subscheme
$Y\hookrightarrow X$ through which $f$ factors, initial among
closed subschemes with this property.

The image is defined by the kernel ideal sheaf of the map
$\mathcal{O}_X\to f_*\mathcal{O}_Z$. The kernel gives both the
factorization and the universal comparison with any other closed
factorization.

## Depends on

- [Closed immersions and closed subschemes](closed-immersions.md)

## Proof depends on

- The kernel ideal sheaf defines the universal closed factorization.

## Sources

- [Hartshorne II.3 (subschemes-and-dimension)](../../../sources/hartshorne-ii-3.md#subschemes-and-dimension)
