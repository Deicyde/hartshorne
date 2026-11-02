---
article_id: af_541d8809de4dba4589651a1e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.properImage
---

# Images of proper schemes

Let $X$ and $Y$ be separated finite-type schemes over a Noetherian scheme
$S$, let $Z \to X$ be a closed subscheme proper over $S$, and let
$f : X \longrightarrow Y$ be an $S$-morphism. Then $f(Z)$ is closed in $Y$, and the scheme-theoretic image
of $Z \longrightarrow Y$ is proper over $S$.

Factor $Z \longrightarrow Y$ through its graph in $Z \times [S] Y$. Separatedness of $Y/S$
makes the graph a closed immersion, while the second projection is a base
change of $Z \longrightarrow S$ and hence proper. Thus $Z \longrightarrow Y$ is proper and has closed
image after every base change. Identify that closed range with the support of
the scheme-theoretic image; descend universal closedness through the resulting
surjective map, while closed immersion into finite-type $Y$ supplies finite
type and separatedness.

## Depends on

- [Schemes over a base](../spectrum-and-schemes/over-base.md)
- [Proper morphisms](proper-morphism.md)
- [The scheme-theoretic image](../subschemes-and-dimension/scheme-theoretic-image.md)
- [Separated morphisms](../separated-morphisms/separated-morphism.md)

## Proof depends on

- [Proper-morphism calculus](proper-morphism-calculus.md)
- [Separated-morphism calculus](../separated-morphisms/separated-morphism-calculus.md)
- Universal closedness descends along a surjective first morphism in a composite.
- The canonical factorization through the scheme-theoretic image.

## Sources

- [Hartshorne II.4, Exercise 4.4](../../../sources/hartshorne-ii-4.md#adopted-exercises)
