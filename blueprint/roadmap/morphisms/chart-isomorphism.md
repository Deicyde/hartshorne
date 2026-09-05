---
declaration: theorem
origin: cited
---

# The charts are isomorphisms of varieties

The chart `φᵢ : Uᵢ → 𝔸ⁿ` of Proposition 2.2 is an isomorphism of varieties, not
merely a homeomorphism (Proposition 3.3).

Only the regular functions remain to be checked. On `Uᵢ` they are locally
quotients of homogeneous polynomials of equal degree in `x₀,…,xₙ`; on `𝔸ⁿ` they
are locally quotients of polynomials in `y₁,…,yₙ`; and the maps `α` and `β` from
the proof of Proposition 2.2 identify the two descriptions.

Small as it is, this node is what transfers Theorem 3.2 to projective varieties.
Without it the chart gives only a homeomorphism, and the counterexamples in
Exercise 3.2 show a homeomorphism carries no information about regular
functions.

## Status

Not proved. The prerequisite that was missing is now in place: `ℙⁿ` is
irreducible, hence itself a projective variety, so `Uᵢ` can be viewed as a
quasi-projective variety at all. See
[projective and quasi-projective varieties](../projective-varieties/projective-variety.md).

What remains is the two morphisms. One direction is cheap: `φᵢ : Uᵢ → 𝔸ⁿ` has
coordinates `x_j/x_i`, ratios of homogeneous polynomials of equal degree, so it
is a morphism by [Lemma 3.6](morphism-to-affine-criterion.md), which is stated
for an arbitrary source. The other direction is not covered by that lemma, since
the target is projective; it has to be checked directly, and the pullback of a
regular function along `β` is where `homogenize` and `dehomogenize` earn their
keep — a ratio of homogeneous polynomials of equal degree in the homogeneous
coordinates becomes a ratio of polynomials in the affine ones, because the
`i`-th coordinate of `β(y)` is `1`.

## Depends on

- [Morphisms](morphism.md)
- [The standard affine charts](../projective-varieties/standard-affine-charts.md)
- [Regular functions on a quasi-projective variety](regular-function-quasi-projective.md)

## Sources

- [Hartshorne I.3, Proposition 3.3 (p. 18)](../../sources/hartshorne.md#i3)
