---
article_id: af_42effd85584b057e482049ca
declaration: def
origin: cited
statement: formalized
lean: Hartshorne.codim
---

# Codimension in a scheme

Codimension takes values in the extended naturals $\mathbb{N} \infty$. For an irreducible
closed subset $Z \subseteq X$, $\operatorname{codim} (Z,X)$ is the supremum of lengths of strict chains
of irreducible closed subsets beginning at $Z$. For a nonempty closed subset
$Y \subseteq X$, $\operatorname{codim} (Y,X)$ is the infimum of $\operatorname{codim} (Z,X)$ over nonempty irreducible
closed subsets $Z \subseteq Y$. Define $\operatorname{codim} (\varnothing ,X) = \infty$, the infimum of the empty
family in $\mathbb{N} \infty$.

Model the irreducible case by the coheight of the corresponding irreducible
closed subset, and use the complete-lattice infimum for the general case.

## Depends on

- [Dimension of a scheme](scheme-dimension.md)

## Proof depends on

- Order coheight and the correspondence between generic points and irreducible closed subsets.

## Sources

- [Hartshorne II.3 (subschemes-and-dimension)](../../../sources/hartshorne-ii-3.md#subschemes-and-dimension)
