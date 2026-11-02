---
article_id: af_9b610e24170abc06369e25d0
declaration: abbrev
origin: cited
statement: formalized
lean: Hartshorne.BirationalMap
---

# Birational maps

A *birational map* $\varphi : X \dashrightarrow Y$ is a rational map admitting an inverse: a
rational map $\psi : Y \dashrightarrow X$ with $\psi\circ\varphi=\mathrm{id}_X$ and $\varphi\circ\psi=\mathrm{id}_Y$ as rational
maps. $X$ and $Y$ are *birationally equivalent*, or simply *birational*, when
one exists.

The equations are equations of *rational* maps, not of maps of sets, and that is
the entire point. $\psi\circ\varphi=\mathrm{id}_X$ says the composite agrees with the identity on
some nonempty open subset of $X$, which by
[Lemma 4.1](morphism-agreement.md) is the strongest thing it could say. Birational
varieties can differ a great deal outside such a subset:
[blowing up](blowing-up.md) is the standard example of a birational morphism
that is not an isomorphism, replacing a point by a whole $\mathbb{P} ^{n-1}$.

Birational equivalence is coarser than isomorphism, and that is what makes it
useful: the classification of varieties up to isomorphism is hopeless, while up
to birational equivalence it becomes the classification of finitely generated
field extensions of $k$, which is [Theorem 4.4](rational-map-function-field.md).

## Depends on

- [Composition of dominant rational maps](rational-map-composition.md)

## Sources

- [Hartshorne I.4, definition of birational map (p. 24)](../../sources/hartshorne.md#i4)
