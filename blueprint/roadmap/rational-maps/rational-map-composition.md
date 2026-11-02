---
article_id: af_50d38585932c26a7be65604d
declaration: definition
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.DominantRatMap.comp
---

# Composition of dominant rational maps

Dominant rational maps compose. If $\varphi : X \dashrightarrow Y$ is represented by
$\langle U, \varphi _U\rangle$ and $\psi : Y \dashrightarrow Z$ by $\langle V, \psi _V\rangle$, then $\varphi _U^{-1}(V)$ is a nonempty open
subset of $X$: dominance is used here because a non-dominant $\varphi$ could have
image disjoint from $V$. Restricting $\varphi _U$ to that preimage and composing with
$\psi _V$ gives a representative of $\psi \circ \varphi$.

This construction is independent of both representatives, is associative, and
has the everywhere-defined identity morphisms as identities. It therefore gives
the category of varieties and dominant rational maps used in Theorem 4.4.

The supporting geometric operation is restriction on both sides: a morphism
$\varphi : A \to B$ and an open $V \subseteq B$ with nonempty preimage induce a morphism from
the open subvariety $\varphi ^{-1}(V)$ of $A$ to the open subvariety $V$ of $B$.

## Depends on

- [Rational maps](rational-map.md)
- [Morphisms](../morphisms/morphism.md)

## Proof depends on

- [Morphisms agreeing on an open set](morphism-agreement.md)

## Sources

- [Hartshorne I.4, rational maps and the category used in Theorem 4.4 (pp. 24–26)](../../sources/hartshorne.md#i4)
