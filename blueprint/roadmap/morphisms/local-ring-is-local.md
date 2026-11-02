---
article_id: af_768cb27118c861e6835ad334
declaration: instance
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.instIsLocalRingLocalRingAt Hartshorne.Variety.instIsLocalRingLocalRingAt
---

# The local ring is local

The ring $\mathcal O_{P,Y}$ is local. Its unique maximal ideal consists
of germs vanishing at $P$, and its residue field is isomorphic to $k$.

If $f(P)\ne0$, the function $f$ is nonzero on some neighbourhood of $P$,
where $1/f$ is regular. Thus its germ is a unit. Every nonunit therefore
belongs to the ideal of germs vanishing at $P$.

Evaluation at $P$ is a surjective homomorphism $\mathcal O_{P,Y}\to k$;
its kernel is the maximal ideal, giving the residue-field identification.
The argument applies to the local ring of any variety.

## Depends on

- [The local ring at a point](local-ring.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, the local ring property of $\mathcal{O} _{P,Y}$ and its residue field (p. 16)](../../sources/hartshorne.md#i3)
