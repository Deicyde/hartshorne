---
article_id: af_211f39a4ee5bfc6bdffb1831
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isSeparated_iff_isClosed_range_diagonal
---

# Closed range of the diagonal

For every scheme morphism $f : X \longrightarrow Y$, the following are equivalent:

1. $f$ is separated;
2. the set-theoretic range of the diagonal morphism of $f$ is closed in
   $X \times [Y] X$.

The diagonal is a homeomorphism onto its range because either projection is a
left inverse. Around a point choose affine neighborhoods $U \subseteq X$ and
$V \subseteq Y$ with $f(U) \subseteq V$; on $U \times [V] U$ the diagonal is the affine closed
immersion from Proposition 4.1. Thus its stalk maps are locally surjective,
and closedness of the range upgrades the preimmersion to a closed immersion.

## Depends on

- [Separated morphisms](separated-morphism.md)

## Proof depends on

- [Affine morphisms are separated](affine-morphism-separated.md)
- An immersion with closed image is a closed immersion.
- The diagonal of a scheme morphism is an immersion.
- Affine neighborhoods form a basis.

## Sources

- [Hartshorne II.4, Corollary 4.2](../../../sources/hartshorne-ii-4.md#separatedness-and-the-valuative-criterion)
