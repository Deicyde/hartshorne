---
article_id: af_0f74f3234bb2bd33998e6fd1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.sheafCohomology_isZero_of_irreducible_dim_zero Hartshorne.preservesFiniteColimits_sheafSectionsOver_top_of_irreducible_dim_zero
---

# The irreducible dimension-zero base case

Let $X$ be an irreducible noetherian space with
$\dim X=0$. Then global sections are exact and
$H^{i}(X,F)=0$ for every abelian sheaf $F$ and every $i>0$.

The proof first shows that the only opens are $\varnothing$ and $X$, so evaluation on
$X$ is an equivalence with abelian groups. The unique main result is the
cohomological vanishing base case.

## Depends on

- [Sheaf cohomology](../sheaf-cohomology.md)

## Proof depends on

- [The long exact sequence of right derived functors](../../derived-functors/right-derived-long-exact-sequence.md)
- [Abelian sheaves have enough injectives](../abelian-sheaves-enough-injectives.md)
- [Flasque closure in short exact sequences](../flasque-short-exact-closure.md)

## Sources

- [Hartshorne III.2, proof of Theorem 2.7, Step 2, printed p. 210](../../../../sources/hartshorne-iii-1-2.md#grothendieck-vanishing-proof-printed-pp-210211)
