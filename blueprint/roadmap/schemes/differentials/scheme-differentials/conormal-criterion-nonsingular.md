---
article_id: af_9373eedb5ff7c51ab189f22d
declaration: theorem
origin: cited
lean: Hartshorne.ConormalCriterion.conormal_criterion_nonsingular
statement: formalized
proof: formalized
---

# The conormal criterion for nonsingularity

Let $Y \hookrightarrow X$ be an irreducible closed subscheme of a nonsingular variety over
an algebraically closed field, with ideal sheaf $J$.  Then $Y$ is nonsingular
if and only if both:

1. $\Omega_{Y/k}$ is locally free; and
2. the conormal sequence is exact on the left.

## Depends on

- [The conormal bundle of a nonsingular closed subvariety](nonsingular-closed-immersion-conormal.md)
- [The conormal sequence of a closed immersion](closed-immersion-conormal-sequence.md)
- [Differentials characterize nonsingular varieties](differentials-characterize-nonsingular.md)

## Proof depends on

- The local dimension inequality for quotients by finitely many generators.
- Construction of a locally generated comparison subscheme and equality of
  integral closed subschemes of the same dimension near a point.

## Sources

- [Hartshorne II.8, Theorem 8.17, printed pp. 178–179](../../../../sources/hartshorne-ii-8.md)
