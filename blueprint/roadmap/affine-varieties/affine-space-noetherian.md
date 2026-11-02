---
article_id: af_509b1e0c7e515812bac12824
declaration: instance
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.instNoetherianSpace
---

# Affine space is a Noetherian space

A topological space is *Noetherian* when its closed subsets satisfy the
descending chain condition. Affine $n$-space with the Zariski topology is
Noetherian.

A descending chain of closed sets $Y_1\supseteq Y_2\supseteq\cdots$ gives
an ascending chain $I(Y_1)\subseteq I(Y_2)\subseteq\cdots$ of ideals in the
Noetherian polynomial ring. The ideal chain stabilizes, and
$Y_i=Z(I(Y_i))$ then shows that the closed-set chain stabilizes.

## Depends on

- [The Zariski topology on affine space](zariski-topology.md)
- [The vanishing ideal](vanishing-ideal.md)

## Sources

- [Hartshorne I.1, definition of Noetherian space and Example 1.4.7 (p. 5)](../../sources/hartshorne.md#i1)
