---
article_id: af_137c79182a944202199147a5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Variety.exists_regularSheafStalkEquivLocalRing
---

# The regular-functions stalk is the local ring

For a variety $X$ and a point $P\in X$, the stalk of the regular-
functions sheaf is canonically isomorphic to the local ring:

$$ (\mathcal{O}_X)_P \cong \mathcal{O}_{P,X}. $$

Both rings consist of germs of regular functions at $P$. The
isomorphism sends a germ to its local-ring class; equality is
determined by agreement on a smaller neighbourhood.

## Depends on

- [The sheaf of regular functions](regular-functions-sheaf.md)
- [Stalks and germs](stalks-and-germs.md)
- [The local ring at a point](../../morphisms/local-ring.md)

## Proof depends on

- The existing germ relation and identity principle for project varieties.

## Sources

- [Hartshorne II.1, identification of the regular-functions stalk with the local ring (p. 62)](../../../sources/hartshorne-ii-1.md#basic-examples-printed-p-62)
