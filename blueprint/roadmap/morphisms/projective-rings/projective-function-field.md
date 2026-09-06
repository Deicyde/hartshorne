---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projFunctionFieldEquiv Hartshorne.projFunctionFieldEquivFractionRing Hartshorne.projFunctionFieldEquivGraded Hartshorne.isDomain_homogeneousCoordinateRing Hartshorne.mk_X_ne_zero Hartshorne.isFractionRing_projAtPrimeBot Hartshorne.isOpen_projNonvanishing Hartshorne.projRatOfFraction Hartshorne.projRatOfFraction_toFun Hartshorne.projRatOfFraction_rel
---

# The function field of a projective variety

**Theorem 3.4(c)**: for `Y` a projective variety meeting the chart `Uᵢ`,

`K(Y) ≅ S(Y)_((0))`.

It is three isomorphisms of fraction fields. `K(Y)` is the fraction field of
`A(Yᵢ)`, which is the geometric half; `A(Yᵢ) ≅ S(Y)_(xᵢ)`; and `S(Y)_((0))` is
the fraction field of `S(Y)_(xᵢ)`. A fraction field is determined by its ring up
to isomorphism, so transporting along the middle isomorphism joins the two ends.

## What Hartshorne compresses

The first of the three is the whole of the reduction to the affine case, and it
is not one step. `K(Y)` for a projective `Y` is a ring that did not exist:
the function field was built in affine coordinates, and had to be rebuilt over
an abstract variety before the statement could be written down. Then it has to
travel from `Y` to the chart piece `Yᵢ` and across the chart isomorphism, which
needs the function field to be functorial for dominant morphisms. Those are
[their own](../function-field-abstract.md)
[nodes](../function-field-functorial.md).

The third is the `𝔭 = (0)` case of the comparison between graded localisations,
on [the graded localisation node](graded-localization.md). That case is the easy
one: the ideal needs no construction, and the prime lying under the maximal
ideal of `S(Y)_((0))` is `(0)` itself, because that ring is a field and the
comparison map is injective.

Two small facts feed it. `S(Y)` is a domain, `J(Y)` being prime for an
irreducible `Y`; and the class of `xᵢ` is nonzero in `S(Y)`, because `xᵢ` does
not vanish at a point of `Y` in the chart. The second is where the hypothesis
that `Y` meets `Uᵢ` is used, and it is the only hypothesis the theorem needs
beyond `Y` being projective.

## A chart-free version is under construction

The isomorphism above is built through a chart, which is what parts (b) and (c)
want. [Part (a)](projective-global-regular.md) needs one that is not, because it
compares readings on different charts and has to know they land on the same
element.

The chart-free route runs the other way: an element of `S(Y)_((0))` is `[g]/[h]`
with `g`, `h` homogeneous of the same degree, and `P ↦ g(P)/h(P)` is directly a
rational function on the open set where `h ≠ 0`
(`Hartshorne.projRatOfFraction`). Nothing is checked beyond two pointwise facts:
the ratio does not see the choice of representative because the degrees agree,
and it is regular because being locally such a ratio *is* the definition of
regular on a projective variety — here it is such a ratio on its whole domain.

Well-definedness is likewise pointwise
(`Hartshorne.projRatOfFraction_rel`): the localisation hands over an equation
`g h' = g' h` in `S(Y)`, an element of `J(Y)` vanishes on `Y`, and cross
multiplication finishes.

What remains is to assemble these into the ring map `S(Y)_((0)) → K(Y)` and show
it bijective. Surjectivity is the definition of regular read backwards;
injectivity is that a nonzero fraction is nonzero somewhere.

## Depends on

- [The function field of an arbitrary variety](../function-field-abstract.md)
- [The function field is functorial for dominant morphisms](../function-field-functorial.md)
- [Graded localization](graded-localization.md)
- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Proof depends on

- [The function field is the fraction field](../function-field-is-fraction-field.md)
- [The charts are isomorphisms of varieties](chart-isomorphism.md)
- [Varieties are covered by affine pieces](../../projective-varieties/affine-cover.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(c) (pp. 18-19)](../../../sources/hartshorne.md#i3)
