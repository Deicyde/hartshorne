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

## Status, and a cost the decision underestimated

The structure exists (`Hartshorne.Variety`) and the **quasi-affine construction
is done** (`Variety.ofQuasiAffine`), which covers the affine case too. Two
refinements were needed along the way and are worth recording:

- Regularity had to be generalised from a subtype inclusion to an arbitrary map
  into affine space (`IsRegularVia`). An open subset of a subset reaches `𝔸ⁿ`
  by a composite of two coercions, and without the generalisation every
  restriction needs transport along `↥U ≃ ↥(val '' U)`.
- Locality was dropped from the structure. Regularity here is defined pointwise,
  so it is local automatically, and carrying it as a field would force
  transporting functions back along inclusions at every construction.

**The quasi-projective construction is blocked.** The same proof that works for
the affine case fails on the `regular` field with a deterministic `whnf`
timeout that does not resolve at four million heartbeats, so it is diverging
rather than merely slow. What has been ruled out: instance search for the
topologies (terminates fast on its own), `abbrev` versus `def` for the coercion
map, `Subalgebra`-membership versus predicate phrasing, and proving restriction
standalone versus inline. Notably the affine construction itself needs a raised
heartbeat limit, and the standalone form of *its* restriction lemma diverges
too — it only compiles inline, where the field pins the expected type. So the
representation is marginal for the affine carrier and over the edge for the
projective one, whose carrier is a quotient type.

That is a genuine cost the design decision underestimated. Before spending more
on it, the options worth weighing are: making `ProjectiveSpace` irreducible so
it cannot unfold into the quotient during unification; giving `Variety` a single
universe parameter; or abandoning the bundled form for §3 and stating the
affine and projective results separately, accepting the duplication the decision
was meant to avoid. This node stays unmarked until one of those lands.

## Depends on

- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)
- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)
- [Regular functions on a quasi-projective variety](regular-function-quasi-projective.md)

## Sources

- [Hartshorne I.3, definition of a variety over `k` (p. 15)](../../sources/hartshorne.md#i3)
