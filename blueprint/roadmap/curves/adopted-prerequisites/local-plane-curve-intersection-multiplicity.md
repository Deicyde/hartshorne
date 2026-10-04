---
article_id: af_5ffc461f2f07008cebf36805
declaration: definition
origin: cited
source_units: [chapter-i-section-5-exercises, chapter-i-section-7-local-comparison]
---

# Local intersection multiplicity of plane curves

For distinct affine plane curves `Y=(f=0)` and `Z=(g=0)` and a point
`P in Y intersect Z`, define

`(Y . Z)_P = length_(O_(A^2,P)) (O_(A^2,P)/(f,g))`.

Prove that this length is finite and at least
`mult_P(Y)*mult_P(Z)`. For all but finitely many lines `L` through `P`, prove
`(L.Y)_P = mult_P(Y)`. Finally, for a projective plane curve `Y` of degree
`d` and a line `L` not contained in `Y`, prove

`sum_(P in L intersect Y) (L.Y)_P = d`.

The local length is the main definition; the three clauses establish the API
needed by tangent lines and flex calculations.

## Depends on

- [Bezout's theorem for distinct plane curves](../../intersections-projective-space/bezout/plane-curve-bezout.md)

## Proof depends on

- Parameter ideals in the regular local ring of the affine plane have finite
  colength.
- The initial homogeneous forms control the length lower bound and the
  exceptional tangent directions.
- The local length agrees with the homogeneous-coordinate intersection
  multiplicity used by Bezout.

## Sources

- [Hartshorne I.5, Exercise 5.4, p.36](../../../sources/hartshorne.md#i7-local-multiplicity-comparison-adopted-for-chapter-iv)
