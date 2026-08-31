---
declaration: def
origin: cited
---

# The local ring at a point

For `P` a point of a variety `Y`, the *local ring* `𝒪_{P,Y}` is the ring of germs
of regular functions near `P`: pairs `(U, f)` with `U` an open neighbourhood of
`P` and `f` regular on `U`, identified when they agree on a common refinement.

It is a local ring: its maximal ideal `𝔪` is the germs vanishing at `P`, since a
germ with `f(P) ≠ 0` has `1/f` regular near `P`, and the residue field
`𝒪_P/𝔪` is `k`.

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
