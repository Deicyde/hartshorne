---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Stein factorization

Let `f : X -> Y` be a projective morphism of Noetherian schemes. With

`Y' = Spec_Y(f_* O_X)`,

there is a factorization

`X -> Y' -> Y`

whose first morphism is projective and has connected fibres and whose second
morphism is finite. The construction satisfies `f'_*O_X ~= O_(Y')`.

## Depends on

- [Direct image of the structure sheaf forces connected fibres](direct-image-units-connected-fibers.md)
- [Coherence of projective higher direct images](../../higher-direct-images/projective-higher-direct-images-coherent.md)
- [Relative Spec of a quasi-coherent algebra](../../../schemes/module-exercises/relative-spec.md)
- [Finite morphisms](../../../schemes/first-properties/finite-morphism.md)
- [Projective-morphism calculus](../../../schemes/proper-and-projective/projective-morphism-calculus.md)

## Proof depends on

- Coherence of `f_*O_X` makes its relative spectrum finite over `Y`.
- The adjunction map factors `f` through `Y'`; since the finite map `Y' -> Y`
  is separated, projectivity cancels from the composite to `X -> Y'`.
- The relative-Spec construction identifies `f'_*O_X` with `O_(Y')`, so the
  connected-fibre criterion applies.

## Sources

- [Hartshorne III.11, Corollary 11.5, p.280](../../../../sources/hartshorne-iii-11-12.md#applications-of-formal-functions-pp279281)
- [Stacks Project, Stein factorization, tag 03H0](../../../../sources/hartshorne-iii-11-12.md#applications-of-formal-functions-pp279281)
