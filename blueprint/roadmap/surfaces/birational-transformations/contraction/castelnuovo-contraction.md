---
article_id: af_04df86bafed55610a72b5ba6
declaration: theorem
origin: cited
source_units: [chapter-v-section-5]
---

# Castelnuovo's contraction theorem

Let `Y` be a curve on a nonsingular projective surface `X` over an
algebraically closed field.  If

`Y ~= P^1` and `Y^2=-1`,

then there are a nonsingular projective surface `X_0`, a point `P` of `X_0`,
and a morphism `f:X->X_0` identifying `X` with the blowup of `X_0` at `P`
and `Y` with its exceptional curve.

This statement and Hartshorne's proof are valid in arbitrary characteristic.
Together with birational-morphism factorization, it also gives the exact
smooth-target criterion: an irreducible curve can be contracted to a
nonsingular point if and only if it is an exceptional curve of the first
kind.

## Depends on

- [The completed local ring at the contraction point is regular](castelnuovo-completed-local-regularity.md)
- [Normalization of the contraction image](castelnuovo-normalized-image.md)
- [Birational morphisms factor into their contracted-curve count of point blowups](../factorization/birational-morphism-point-blowup-factorization.md)

## Proof depends on

- The constructed morphism contracts exactly one irreducible curve, so its
  contracted-curve count is one.  The factorization theorem therefore makes
  it one point blowup.

## Sources

- [Hartshorne V.5, Theorem 5.7, Steps 1–6, pp.414–416](../../../../sources/hartshorne-v-5.md)
