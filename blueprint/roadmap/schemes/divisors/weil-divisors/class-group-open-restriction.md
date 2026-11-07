---
article_id: af_af78109c23021852fb9a08c2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.weilClassGroupRestrict AlgebraicGeometry.Scheme.weilClassGroupRestrict_surjective AlgebraicGeometry.Scheme.weilClassGroupRestrict_bijective_of_two_le_codim AlgebraicGeometry.Scheme.weilClassGroupRestrict_exact_of_codim_eq_one
---

# Restriction of class groups to open complements

Let $X$ satisfy $(*)$, let $Z$ be a proper closed subset, and set
$U = X - Z$. Restricting prime divisors defines a surjection
$\operatorname{Cl} X \to \operatorname{Cl} U$. It is an isomorphism when $\operatorname{codim} (Z,X) \ge 2$; when $Z$ is
irreducible of codimension one, the sequence
$\mathbb{Z} \to \operatorname{Cl} X \to \operatorname{Cl} U \to 0$, with $1 \mapsto [Z]$, is exact.

The three clauses are one localization theorem, with a single completion
criterion: identify the kernel as classes supported on the complement.

## Depends on

- [Linear equivalence and the Weil class group](weil-linear-equivalence.md)
- [Codimension in a scheme](../../subschemes-and-dimension/scheme-codimension.md)

## Proof depends on

- A prime divisor on $U$ is the intersection with $U$ of its closure in $X$.
- The function fields of $X$ and a nonempty open subscheme agree.

## Sources

- [Hartshorne II.6, Proposition 6.5 on printed p.133](../../../../sources/hartshorne-ii-6.md#weil-divisors-and-class-groups)
