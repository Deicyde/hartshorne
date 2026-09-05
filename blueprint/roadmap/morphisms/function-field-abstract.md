---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Variety.RationalRep Hartshorne.Variety.RationalRep.Rel Hartshorne.Variety.RationalRep.rel_trans Hartshorne.Variety.FunctionField Hartshorne.Variety.opens_inter_nonempty Hartshorne.Variety.dense_of_isOpen_of_nonempty Hartshorne.Variety.instCommRingFunctionField Hartshorne.Variety.instFieldFunctionField Hartshorne.Variety.isField_functionField Hartshorne.ratRepToVariety Hartshorne.ratRepOfVariety Hartshorne.functionFieldEquivAffine
---

# The function field of an arbitrary variety

`K(X)` for a bundled `Variety`, together with its field structure, and the
statement that for a quasi-affine `Y` it agrees with the affine construction.

Theorem 3.4(c) is about `K(Y)` for a *projective* `Y`, and the affine
construction is stated in affine coordinates, so this is the same repetition the
germ construction went through. As there, the abstract version is shorter, since
everything it needs is a field of `Variety` rather than a fact about
polynomials.

## Why `K(X)` is a field and `𝒪_P` is only local

The two constructions differ in one clause — whether the domain must contain a
fixed point — and that clause is the entire difference between a local ring and
a field.

A germ is invertible when it is nonzero *at `P`*. That is strictly stronger than
being a nonzero germ, and the germs that fail it are exactly the maximal ideal.
A rational function is invertible as soon as it is nonzero, because "nonzero"
already means "nonzero somewhere": the locus where it is nonzero is open, and
can be taken as the new domain. Nothing is lost by shrinking the domain, because
a rational function is not attached to any point.

Everything else in the construction is irreducibility, used three times: sums
and products intersect domains and the intersection must be nonempty;
transitivity of the identification needs the triple overlap to be nonempty too.
In the germ case all three were free, since every domain contained `P`.

## The comparison with the affine construction

For a quasi-affine `Y` the two are the same field
(`Hartshorne.functionFieldEquivAffine`), and there is nothing in the proof: a
representative is a nonempty open set carrying a regular function, `regular` on
`Variety.ofQuasiAffine hY` is by definition `IsRegularVia` in the affine
coordinates, and the only difference is how the open set is packaged.

This is easier than the corresponding comparison for germs, which needed the
point spelled `⟨P.1, P.2⟩` to get instance search to find the ring structure on
both sides. With no point in the statement, that problem does not exist.

## Depends on

- [The function field](function-field.md)
- [Varieties](variety.md)

## Proof depends on

- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)

## Sources

- [Hartshorne I.3, definition of `K(Y)` (p. 16)](../../sources/hartshorne.md#i3)
