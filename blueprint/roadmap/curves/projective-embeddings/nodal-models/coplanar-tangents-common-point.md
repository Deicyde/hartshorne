---
declaration: theorem
origin: cited
source_units: [chapter-iv-section-3]
---

# Coplanar tangents have a common point

Let `X subset P^3` be a nonplanar curve. If the tangent lines at every pair of
points are coplanar, then there is a point `A in P^3` lying on every tangent
line of `X`.

## Depends on

- [Secant and tangent incidence](../linear-series/secant-tangent-incidence-api.md)

## Proof depends on

- If all tangent lines coincide the conclusion is immediate. Otherwise,
  choose two distinct tangent lines and their intersection `A`. Outside the
  finite intersection with their spanning plane, every tangent meets both
  lines and hence passes through `A`.
- Incidence with a fixed point is closed, so the conclusion extends from the
  resulting nonempty open subset to all of `X`.

## Sources

- [Hartshorne IV.3, second half of Proposition 3.8, p.311](../../../../sources/hartshorne-iv-3.md#nodal-projections-and-bad-secants-pp310314)
