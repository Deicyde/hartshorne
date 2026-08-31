---
declaration: def
origin: cited
---

# The function field

The *function field* `K(Y)` of a variety `Y` consists of equivalence classes of
pairs `(U, f)` with `U` a nonempty open subset and `f` regular on `U`, where
`(U, f)` and `(V, g)` are identified when `f = g` on `U ∩ V`. Its elements are
the *rational functions* on `Y`.

`K(Y)` is a field. Addition and multiplication are defined because `Y` is
irreducible, so any two nonempty open sets meet; inverses exist because a nonzero
`(U, f)` restricts to `V = U ∖ Z(f)`, which is nonempty and on which `1/f` is
regular. Irreducibility is doing real work here and is the reason Hartshorne's
varieties are irreducible by definition.

Restriction gives injections `𝒪(Y) ↪ 𝒪_P ↪ K(Y)`, by the identity principle, and
this node should establish them: the rest of the section treats all three as
subrings of `K(Y)` without comment.

## Depends on

- [The ring of regular functions](ring-of-regular-functions.md)
- [The local ring at a point](local-ring.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, definition of `K(Y)` and the injections into it (p. 16)](../../sources/hartshorne.md#i3)
