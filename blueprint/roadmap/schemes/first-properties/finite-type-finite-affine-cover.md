---
article_id: af_87419a940773431b5efc1fd9
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
statement: formalized
proof: formalized
lean: Hartshorne.finiteType_iff_everyAffineTarget
---

# The finite affine-cover criterion for finite type

A morphism `f : X → Y` is finite type if and only if, for every affine open
`V = Spec B` in `Y`, the inverse image `f⁻¹(V)` has a finite affine cover
`Spec A_i` with each `A_i` a finitely generated `B`-algebra.

Combine the affine-target criterion for local finite type with the criterion
that quasi-compactness is detected on affine target inverse images.

## Depends on

- [The affine-target criterion for local finite type](locally-finite-type-affine-target-criterion.md)
- [Morphisms of finite type](finite-type.md)
- [Quasi-compact morphisms](quasi-compact-morphism.md)

## Proof depends on

- Finite affine refinements of quasi-compact open covers.

## Sources

- [Hartshorne II.3, Exercise 3.3(b) (p. 91)](../../../sources/hartshorne-ii-3.md#finite-type-and-finite-morphisms)
