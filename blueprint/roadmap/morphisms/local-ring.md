---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.GermRep Hartshorne.GermRep.Rel Hartshorne.GermRep.rel_trans Hartshorne.isRegularVia_restrict Hartshorne.preirreducible_univ_of_isOpen
---

# The local ring at a point

For `P` a point of a variety `Y`, the *local ring* `𝒪_{P,Y}` is the ring of germs
of regular functions near `P`: pairs `(U, f)` with `U` an open neighbourhood of
`P` and `f` regular on `U`, identified when they agree on a common refinement.

That it deserves the name — that `𝒪_{P,Y}` is a local ring with maximal ideal
the germs vanishing at `P`, and residue field `k` — is a theorem and lives in
[its own article](local-ring-is-local.md). This node is the construction and its
ring structure.

Well-definedness of the identification is where Remark 3.1.1 is used —
transitivity of the relation needs that two regular functions agreeing on a
nonempty open set agree on the overlap of their domains — which is why the
continuity node is a proof prerequisite rather than an aside.

## Depends on

- [The ring of regular functions](ring-of-regular-functions.md)
- [Varieties](variety.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, definition of the local ring `𝒪_{P,Y}` (p. 16)](../../sources/hartshorne.md#i3)
