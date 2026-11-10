---
article_id: af_f44c38ec3ee73430940f4f25
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.sheafCohomology_isZero_of_isFlasque Hartshorne.isRightAcyclic_sheafSectionsOver_top_of_isFlasque
---

# Flasque sheaves are acyclic

If $F$ is a flasque abelian sheaf on $X$, then $H^{n}(X,F)=0$ for every
positive degree $n$.

Embed $F$ into an injective abelian sheaf, use the flasque quotient lemma and
surjectivity on global sections, and dimension-shift along the long exact
cohomology sequence. This is the unique main vanishing result.

## Depends on

- [Sheaf cohomology](sheaf-cohomology.md)
- [Acyclic resolutions compute derived functors](../derived-functors/acyclic-resolution-comparison.md)

## Proof depends on

- [Abelian sheaves have enough injectives](abelian-sheaves-enough-injectives.md)
- [Injective abelian sheaves are flasque](injective-abelian-sheaf-flasque.md)
- [Flasque closure in short exact sequences](flasque-short-exact-closure.md)
- [The long exact sequence of right derived functors](../derived-functors/right-derived-long-exact-sequence.md)

## Sources

- [Hartshorne III.2, Proposition 2.5 and Remark 2.5.1, printed p. 208](../../../sources/hartshorne-iii-1-2.md#enough-injectives-and-cohomology-printed-pp-206208)
