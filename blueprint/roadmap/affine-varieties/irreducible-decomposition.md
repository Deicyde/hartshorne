---
article_id: af_3a1b61ce82b649c859736803
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_unique_irredundant_decomposition Hartshorne.IsAlgebraicSet.exists_unique_decomposition Hartshorne.IsIrreducible.exists_mem_subset_of_subset_biUnion Hartshorne.irredundant_decomposition_unique
---

# Decomposition into irreducible components

In a Noetherian topological space, every nonempty closed subset $Y$ is a
finite union

$$Y=Y_1\cup\cdots\cup Y_r$$

of irreducible closed subsets. If no $Y_i$ contains another, the subsets
$Y_i$ are uniquely determined and are called the *irreducible components*
of $Y$.

In particular, every algebraic set in affine space has a unique
irredundant decomposition into finitely many varieties. This is
Hartshorne's Corollary I.1.6.

Existence follows by Noetherian induction on closed subsets. For uniqueness,
an irreducible component in one decomposition must lie in a component of
the other; applying this in both directions and using irredundancy gives
equality of the components.

## Depends on

- [Affine space is a Noetherian space](affine-space-noetherian.md)
- [Affine and quasi-affine varieties](affine-variety.md)

## Sources

- [Hartshorne I.1, Proposition 1.5 and Corollary 1.6 (p. 5)](../../sources/hartshorne.md#i1)
