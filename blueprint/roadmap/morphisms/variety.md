---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Variety Hartshorne.Variety.ofQuasiAffine Hartshorne.Variety.ofQuasiProjective Hartshorne.Variety.ofProjective Hartshorne.regularSubalgebra Hartshorne.projRegularSubalgebra Hartshorne.Variety.eq_of_eqOn Hartshorne.Variety.preirreducible_univ
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
- Locality was then put back, together with two more fields, and the earlier
  reasoning turned out to be the wrong way round. "Regularity is defined
  pointwise, so locality is free" is true of every construction and useless for
  an abstract variety, which has no definition to appeal to.
  [Lemma 3.6](morphism-to-affine-criterion.md) forced the correction: it is
  stated for an arbitrary source and needs three things a `Subalgebra` does not
  give — closed zero loci, closure under division by a nowhere-zero regular
  function, and locality. All three are Lemma 3.1 or the pointwise definition in
  each of the four constructions, so the cost was small; the mistake was
  reasoning about what the constructions satisfy instead of about what the
  abstract structure exposes.

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

## The identity principle, once instead of twice

Remark 3.1.1 was proved separately in affine and in projective coordinates, each
time from Lemma 3.1. With the fields Lemma 3.6 forced, it can be proved once for
any `Variety` and from the structure alone: regular functions form a subalgebra,
so the difference of two is regular; the zero locus of a regular function is
closed; and a nonempty open subset of an irreducible space is dense. No
polynomial appears.

This is what makes germs and the function field constructible for an arbitrary
variety rather than separately in each set of coordinates, which is what
Theorem 3.4 will need — it is about `𝒪_P` and `K(Y)` for a projective `Y`, and
those exist so far only in the affine case.

## Depends on

- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)
- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)
- [Regular functions on a quasi-projective variety](regular-function-quasi-projective.md)

## Sources

- [Hartshorne I.3, definition of a variety over `k` (p. 15)](../../sources/hartshorne.md#i3)
