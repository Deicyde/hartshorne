---
article_id: af_3eef3cf7ecf8c4deb15fbf7b
declaration: definition
origin: cited
source_units: [chapter-iii-sections-8-9]
statement: formalized
proof: formalized
lean: Hartshorne.InfinitesimalDeformation Hartshorne.closedFiberBaseChangeIso Hartshorne.InfinitesimalDeformation.ofFamilyLift Hartshorne.InfinitesimalDeformation.ofFamilyTangent
---

# Infinitesimal deformations over the dual numbers

For `D=k[t]/(t^2)`, define an infinitesimal deformation of a finite-type
`k`-scheme `X` to consist of a `D`-scheme `X'`, a proof that `X' -> Spec D`
is flat, and a chosen isomorphism from the closed fibre
`X' times_(Spec D) Spec k` to `X`. The closed-fibre isomorphism is part of the
structure, not an unrecorded existence proposition.

If `W -> T` is a flat global family, `t : T`, and the marked fibre `W_t` is
identified with `X`, then a tangent vector `Spec D -> T` based at `t` gives an
infinitesimal deformation with its induced closed-fibre marking.

## Depends on

- [The stalk criterion for flat morphisms](../flatness/flat-morphism-stalk-criterion.md)
- [The fibre of a morphism](../../../schemes/fiber-products/scheme-fiber.md)
- [Tangent vectors and the dual numbers](../../../schemes/foundational-properties/tangent-vectors-dual-numbers.md)

## Proof depends on

- The dual-number ring in `Mathlib/RingTheory/DualNumber.lean`.
- [Flat morphisms are stable under base change](../flatness/flat-morphism-base-change.md).
- Compatibility of the fibre pullback with the composite `Spec k -> Spec D -> T`.

## Sources

- [Hartshorne III.9, Example 9.13.1, p.265](../../../../sources/hartshorne-iii-9.md#infinitesimal-deformations-pp265266)
