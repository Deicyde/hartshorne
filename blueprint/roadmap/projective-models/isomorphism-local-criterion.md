---
article_id: af_4d70319a29a0ec29f2c79a20
declaration: theorem
origin: cited
source_units: [exercise-i-3-3]
statement: formalized
proof: formalized
lean: Hartshorne.VarietyHom.isIso_iff_isHomeomorph_and_bijective_localRingHom
---

# Isomorphisms from topology and local rings

Let `φ : X → Y` be a morphism. Then `φ` is an isomorphism of varieties if
and only if its underlying map is a homeomorphism and every induced map
`𝒪_{φ(P),Y} → 𝒪_{P,X}` is bijective. The sole main declaration is planned as
`Hartshorne.VarietyHom.isIso_iff_isHomeomorph_and_bijective_localRingHom`.

This is exactly Exercise 3.3(b), not merely its difficult sufficient
direction. For that direction, the proof builds the inverse continuously from
the homeomorphism and checks regularity locally through the inverse stalk
maps; the converse uses the already-formalized local-ring functoriality of an
isomorphism.

## Depends on

- [Morphisms](../morphisms/morphism.md)
- [The local ring is functorial](../morphisms/local-ring-functorial.md)

## Proof depends on

- [Criterion for a morphism to an affine variety](../morphisms/morphism-to-affine-criterion.md)
- [Regular functions on a quasi-projective variety](../morphisms/regular-function-quasi-projective.md)

## Sources

- [Hartshorne I.3, Exercise 3.3(b) (p. 21)](../../sources/hartshorne.md#i3)
