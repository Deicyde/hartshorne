---
declaration: theorem
origin: cited
source_units: [chapter-v-section-5]
---

# Hironaka's negative elliptic curve is not algebraically contractible

Over an uncountable algebraically closed field `k`, there are ten
`Z`-independent points `P_1,...,P_10` on a nonsingular plane cubic `Y_0`,
with an inflection point as origin.  On the blowup of `P^2` at those points,
the strict transform `Y` is a genus-one curve with

`Y^2=9-10=-1`,

but `Y` is not algebraically contractible.

For noncontractibility, an affine neighborhood of a hypothetical contraction
point supplies a curve avoiding that point.  Its plane image `C` meets `Y_0`
only at the ten marked points.  If `d=deg C`, Bézout and the elliptic group
law give

`sum_i n_i P_i=0`, with `n_i>=0` and `sum_i n_i=3d>0`,

contradicting `Z`-independence.  The choice of points uses that `Y_0(k)` is
uncountable while its torsion subgroup is countable; finiteness of each
`n`-torsion fibre is required in every characteristic.

## Depends on

- [Contractible curves](contractible-curve-definition.md)
- [The intersection form on the projective plane](../../intersection-theory/examples-adjunction/projective-plane-intersection-form.md)
- [The total-transform formula](../../monoidal-transformations/strict-transforms/divisor-total-transform-formula.md)
- [Intersection with the exceptional curve](../../monoidal-transformations/strict-transforms/strict-transform-exceptional-intersection.md)
- [Bézout's theorem for distinct plane curves](../../../intersections-projective-space/bezout/plane-curve-bezout.md)
- [Collinearity and the elliptic-curve group law](../../../curves/elliptic-curves/group-law-foundations/elliptic-collinearity-group-law.md)
- [Points on a genus-one curve and its degree-zero Picard group](../../../curves/riemann-roch/elliptic-points-picard-zero.md)
- [Integer multiplication is a morphism](../../../curves/elliptic-curves/group-law-foundations/elliptic-integer-multiplication-morphism.md)

## Proof depends on

- A finite nonconstant map from the cubic to `P^1` shows that its set of
  `k`-points has the cardinality of the uncountable field.  For every nonzero
  integer `n`, the all-characteristic theorem `deg[n]=n^2` makes the
  multiplication fibre over the origin finite, including when the
  characteristic divides `n`; hence the union of all torsion fibres is
  countable and ten independent points can be chosen successively.
- Choose the auxiliary curve in the affine neighborhood so that its inverse
  image is not one of the finitely many exceptional curves of the plane
  blowup.

## Analytic comparison

- [Grauert's theorem](grauert-analytic-negative-curve-contraction.md) makes
  this curve analytically contractible when `k=C`.  This is intentionally not
  a typed dependency of the algebraic noncontractibility result.

## Sources

- [Hartshorne V.5, Hironaka's Example 5.7.3, p.417](../../../../sources/hartshorne-v-5.md)
- Silverman, *The Arithmetic of Elliptic Curves*, III.6.2, for
  all-characteristic finiteness and degree of `[n]`.
