---
article_id: af_336eb54287251594421bfd3b
declaration: theorem
origin: cited
source_units: [exercise-i-3-3]
statement: formalized
proof: formalized
lean: Hartshorne.VarietyHom.injective_localRingHom_of_denseRange
---

# Dense morphisms inject on local rings

Let `φ : X → Y` be a morphism of varieties with dense image and let `P ∈ X`.
Then the induced map

`φ* : 𝒪_{φ(P),Y} → 𝒪_{P,X}`

is injective.  This is Exercise 3.3(c), and the sole main declaration is
planned as `Hartshorne.VarietyHom.injective_localRingHom_of_denseRange`.

## Depends on

- [Morphisms](../morphisms/morphism.md)
- [The local ring is functorial](../morphisms/local-ring-functorial.md)

## Proof depends on

- [The underlying maps into germs and rational functions are injective](../morphisms/function-field-injections.md)
- [The function field is functorial for dominant morphisms](../morphisms/function-field-functorial.md)

## Sources

- [Hartshorne I.3, Exercise 3.3(c) (p. 21)](../../sources/hartshorne.md#i3)
