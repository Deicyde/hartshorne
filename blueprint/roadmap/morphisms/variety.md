---
declaration: def
origin: cited
---

# Varieties

Hartshorne's definition on p. 15 is that a *variety* over `k` is any affine,
quasi-affine, projective or quasi-projective variety. It is a bookkeeping
definition, but it is the one that lets §3 state Theorem 3.2, Proposition 3.5
and Lemma 3.6 for an arbitrary variety `X` while constraining only `Y`. Getting
it wrong forces every later statement to be quadrupled.

**Design decision, fixed here rather than left to Lean review:** `Variety` is a
structure bundling a topological space with, for each open subset, a `k`-algebra
of functions on it designated regular, subject to the locality conditions the
§3 definitions satisfy. The four cases of Hartshorne's definition then become
four constructions of that structure rather than four constructors of an
inductive type.

The alternative, an inductive sum of the four cases, was rejected: every
statement quantifying over varieties would need a four-way case split, and
nothing in §3 ever distinguishes the cases except Theorem 3.4, which is stated
about projective varieties specifically. The bundled form is also the shape
Chapter II's locally ringed spaces take, so the classical layer will not have to
be rebuilt to connect to it. The cost is real and is charged to this node:
proving that each of the four kinds satisfies the structure, which the two
regular-function articles supply and which is why they are prerequisites for
*stating* this definition rather than only for its proofs.

## Depends on

- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)
- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)
- [Regular functions on a quasi-projective variety](regular-function-quasi-projective.md)

## Sources

- [Hartshorne I.3, definition of a variety over `k` (p. 15)](../../sources/hartshorne.md#i3)
