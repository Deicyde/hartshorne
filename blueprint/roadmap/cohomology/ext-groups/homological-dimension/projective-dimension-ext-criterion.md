---
article_id: af_95ed156bd0241f4391ff6e6e
declaration: theorem
origin: cited
mathlib: true
mathlib_declaration: CategoryTheory.hasProjectiveDimensionLT_iff
mathlib_file: Mathlib/CategoryTheory/Abelian/Projective/Dimension.lean
---

# Projective-dimension bounds detected by Ext

For an object $M$ in an abelian category in which Ext groups exist,
and a natural number $n$, having projective dimension less than
$n$ is equivalent to

$\forall i \ge n, \forall N, \operatorname{Ext} ^i(M,N)=0$.

Consequently, projective dimension at most $n$ is equivalent to
vanishing in every degree $i>n$. For modules this is Hartshorne's
condition $\operatorname{pd}(M)\le n$. The case $n=0$ says that
$M$ is projective exactly when $\operatorname{Ext}^1(M,N)=0$ for
every $N$.

## Depends on

- [Global Ext groups](../global-ext/global-ext-groups.md)

## Sources

- [Hartshorne III.6, Proposition 6.10A, printed p.237](../../../../sources/hartshorne-iii-6.md#quoted-homological-algebra-printed-pp236237)
- Matsumura [2], pp.127–128, as cited by Hartshorne.
