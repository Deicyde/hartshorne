---
article_id: af_0fdccec34faa6f6a85264973
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-abstract-curves]
---

# The valuation-space regularity axioms

The regular-function algebras on open subsets of `C_K` satisfy the four axioms
required by `Hartshorne.Variety`:

1. regular functions restrict to smaller opens;
2. the zero locus of a regular function is closed;
3. a quotient by a nowhere-zero regular function is regular; and
4. regularity is local.

Restriction is monotonicity of intersections.  A nonzero rational function
has only finitely many zero valuations, so its zero locus is finite; the zero
function has the whole open set as zero locus.  If the residue of a denominator
is nonzero at `R`, that denominator is a unit of the local ring `R`, giving the
division axiom.

For locality, choose one local rational representative.  Any other local
representative agrees with it on a nonempty intersection of cofinite opens, so
injectivity of evaluation makes the two elements of `K` equal.  The chosen
representative therefore belongs to every valuation ring over the original
open and represents the whole function.

State these properties as one structure-shaped theorem so the following
definition of an abstract curve contains no new mathematical proof.

## Depends on

- [Regular functions on the valuation space](valuation-regular-functions.md)

## Proof depends on

- [A rational function has finitely many poles](finite-poles.md)

## Sources

- [Hartshorne I.6, regular functions on `C_K` and their identification with functions (p. 42)](../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
