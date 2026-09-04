---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.RationalRep Hartshorne.RationalRep.Rel Hartshorne.RationalRep.rel_trans Hartshorne.inter_nonempty Hartshorne.GermRep.toRationalRep
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

Note that `K(Y)` is defined without reference to `𝒪_P`: both are equivalence
classes of pairs `(U, f)`, differing only in whether `U` is required to contain a
fixed point. The comparison between them is
[a separate article](function-field-injections.md), so this node depends on
neither the local ring nor the global sections.

## Depends on

- [Varieties](variety.md)
- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)
- [Regular functions on a quasi-projective variety](regular-function-quasi-projective.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, definition of `K(Y)` (p. 16)](../../sources/hartshorne.md#i3)
