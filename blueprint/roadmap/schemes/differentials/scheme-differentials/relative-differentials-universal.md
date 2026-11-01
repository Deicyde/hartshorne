---
article_id: af_06e9acaca163bf53920d3e2e
declaration: theorem
origin: bridged
lean: AlgebraicGeometry.Scheme.relativeDifferentials_universal
statement: formalized
proof: formalized
---

# The universal property of the relative differential sheaf

For a scheme morphism `f : X → Y` and an `𝒪_X`-module `M`, composition with
the canonical derivation gives a natural equivalence between
`𝒪_X`-linear morphisms

`Ω[X/Y] → M`

and derivations `𝒪_X → M` that vanish on the image of
`f⁻¹𝒪_Y → 𝒪_X`. This equivalence is natural in `M` and uniquely characterizes
the relative differential sheaf together with its derivation.

## Depends on

- [The relative differential sheaf](relative-differentials.md)
- [Pushforward, pullback, and their adjunction](../../modules-and-quasicoherent/module-push-pull-adjunction.md)

## Proof depends on

- The sheafification adjunction composed with the universal property of
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`.

## Sources

- [Hartshorne II.8, differential modules and the scheme differential sheaf (pp. 172–176)](../../../../sources/hartshorne-ii-8.md#modules-and-sheaves-of-differentials)
