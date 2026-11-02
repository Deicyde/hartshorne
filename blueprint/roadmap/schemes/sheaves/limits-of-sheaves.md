---
article_id: af_8197f6c713ed2d28d1473bba
declaration: theorem
origin: cited
mathlib: true
mathlib_declaration: CategoryTheory.Sheaf.isSheaf_of_isLimit
mathlib_file: Mathlib/CategoryTheory/Sites/Limits.lean
---

# Limits of sheaves are computed pointwise

The category of sheaves of abelian groups admits products and inverse limits,
and the underlying presheaf of such a limit is the pointwise limit. In
particular, for an inverse system $\{F_{i}\}$ and every open $U$,

$(\lim F_{i})(U) \cong \lim F_{i}(U)$.

A pointwise limit of sheaves satisfies the sheaf condition. Thus the
forgetful functor to presheaves creates these limits. Products and
inverse limits are the cases used in Hartshorne's Exercises II.1.9
and II.1.12.

## Depends on

- [Sheaves of abelian groups](sheaves-of-abelian-groups.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, Exercises 1.9 and 1.12 (pp. 66–67), used on p. 109 and in Proposition 9.2](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)

