---
article_id: af_2ee7948708b181e79fc71226
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.LocalRingAt Hartshorne.Variety.LocalRingAt Hartshorne.localRingEquivAffine
---

# The local ring at a point

For a point $P$ of a variety $Y$, the *local ring* $\mathcal O_{P,Y}$
is the ring of germs of regular functions near $P$. A germ is represented
by a pair $(U,f)$, where $U$ is an open neighbourhood of $P$ and $f$ is
regular on $U$. Representatives are identified when they agree on a
common neighbourhood of $P$.

Addition and multiplication use intersections of neighbourhoods. The
identity principle also identifies this local agreement relation with
agreement on the full overlap of representatives.

[The local-ring theorem](local-ring-is-local.md) identifies its maximal
ideal and residue field. For a quasi-affine variety this construction
agrees canonically with the one in affine coordinates; it also applies
to projective varieties. [Functoriality](local-ring-functorial.md) compares
local rings along morphisms and open inclusions.

## Depends on

- [The ring of regular functions](ring-of-regular-functions.md)
- [Varieties](variety.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, definition of the local ring $\mathcal{O} _{P,Y}$ (p. 16)](../../sources/hartshorne.md#i3)
