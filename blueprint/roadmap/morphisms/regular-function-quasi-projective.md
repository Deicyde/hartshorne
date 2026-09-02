---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.IsRegularAtProj Hartshorne.IsRegularProj Hartshorne.ratio_eq_of_smul Hartshorne.isClosed_eqLocusProj
---

# Regular functions on a quasi-projective variety

Let `Y ⊆ ℙⁿ` be quasi-projective. A function `f : Y → k` is *regular at* `P` when
there is an open `U` with `P ∈ U ⊆ Y` and homogeneous `g, h ∈ S` **of the same
degree** with `h` nowhere zero on `U` and `f = g/h` on `U`.

Equal degrees is the whole point: neither `g` nor `h` is a function on `ℙⁿ`, but
their ratio is, because the scaling factors `λᵈ` cancel. Dropping the condition
makes the definition meaningless rather than merely wrong.

Continuity and the identity principle hold here by the same argument as in the
quasi-affine case; Hartshorne leaves the repetition to the reader. In Lean it is
worth asking whether the two definitions can be stated once against a common
interface rather than twice, since §3 immediately treats them uniformly.

## Depends on

- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)

## Sources

- [Hartshorne I.3, definition of a regular function on a quasi-projective variety (p. 15)](../../sources/hartshorne.md#i3)
