---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Variety Hartshorne.Variety.ofQuasiAffine Hartshorne.Variety.ofQuasiProjective Hartshorne.Variety.ofProjective Hartshorne.regularSubalgebra Hartshorne.projRegularSubalgebra
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

## Status

The structure exists (`Hartshorne.Variety`) and **all four of Hartshorne's cases
are constructed**: `Variety.ofQuasiAffine` covers affine and quasi-affine,
`Variety.ofQuasiProjective` and `Variety.ofProjective` cover the other two. Two
refinements were needed along the way and are worth recording:

- Regularity had to be generalised from a subtype inclusion to an arbitrary map
  into affine space (`IsRegularVia`). An open subset of a subset reaches `𝔸ⁿ`
  by a composite of two coercions, and without the generalisation every
  restriction needs transport along `↥U ≃ ↥(val '' U)`.
- Locality was dropped from the structure. Regularity here is defined pointwise,
  so it is local automatically, and carrying it as a field would force
  transporting functions back along inclusions at every construction.

The quasi-projective construction was blocked for a while by an elaboration
divergence that also affected the affine one. The cause turned out to have
nothing to do with the representation: restriction lemmas were applying a
hypothesis as `hne _ hx`, and with a metavariable the elaborator cannot match
the two subtype coercions syntactically, falls back on unfolding `eval` over
`MvPolynomial`, and never terminates. Supplying the point explicitly,
`hne ⟨x.1, hUV x.2⟩ hx`, makes the conclusion match by cheap definitional
equality. The two forms are mathematically identical.

So the bundled representation is fine after all, and the cost it charges is the
four constructions, as originally estimated. The episode is recorded because the
symptom pointed hard at the representation and at the projective quotient
carrier, and both were red herrings.

## Depends on

- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)
- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)
- [Regular functions on a quasi-projective variety](regular-function-quasi-projective.md)

## Sources

- [Hartshorne I.3, definition of a variety over `k` (p. 15)](../../sources/hartshorne.md#i3)
