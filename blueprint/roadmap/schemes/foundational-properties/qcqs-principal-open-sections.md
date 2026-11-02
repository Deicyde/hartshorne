---
article_id: af_777bdab39564bd4ef93338be
declaration: theorem
origin: cited
mathlib: true
mathlib_declaration: AlgebraicGeometry.isLocalization_basicOpen_of_qcqs
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean
---

# The qcqs principal-open lemma

Let $U$ be a quasi-compact, quasi-separated open of a scheme $X$ and
$f \in \Gamma (U,\mathcal{O} _X)$.  Define

$U_f = \{x \in U | f_x \notin \mathfrak{m} _x\}$,

where $f_x$ is the germ and $\mathfrak{m} _x$ the maximal ideal of the local ring.  This
is the principal open determined by $f$.  Restriction exhibits its sections as
the localization

$\Gamma (U_f,\mathcal{O} _X) \cong \Gamma (U,\mathcal{O} _X)_f$.

This is the quasi-compact, quasi-separated form of Hartshorne's
Exercise II.2.16(b–d). Injectivity is the power-torsion statement,
which requires only quasi-compactness. Surjectivity follows by
gluing common-power multiples over a finite affine cover.

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)
- [Open subschemes](../spectrum-and-schemes/open-subscheme.md)

## Sources

- [Hartshorne II.2, Exercise 2.16(a–d), used on p. 82 and generalized by Lemma 5.14 on p. 118](../../../sources/hartshorne-ii-2.md#exercises-212-through-219)
