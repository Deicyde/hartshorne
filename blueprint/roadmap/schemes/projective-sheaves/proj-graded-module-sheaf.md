---
article_id: af_a1514e0312b258aa9beb8176
declaration: def
origin: cited
source_units: [chapter-ii-section-5]
---

# The sheaf of a graded module on Proj

For a graded ring `S` and graded `S`-module `M`, construct an
`O_{Proj S}`-module `M~` whose germ at a homogeneous prime `p` is the
degree-zero part `M_(p)` of the homogeneous localization. For every positive-
degree homogeneous `f`, identify

`M~|_{D₊(f)} ≅ (M_(f))~`

under `D₊(f) ≅ Spec S_(f)`. Deduce that `M~` is quasi-coherent and, when `S`
is Noetherian and `M` finite, coherent.

The chart and stalk formulas characterize the construction and are bundled
with it so subsequent nodes do not depend on an underspecified sheaf.

## Depends on

- [The structure sheaf on Proj](../projective-spectrum/proj-structure-sheaf.md)
- [A standard Proj chart is affine](../projective-spectrum/proj-basic-open.md)
- [Sheaves of modules](../modules-and-quasicoherent/sheaves-of-modules.md)
- [Quasi-coherence by local presentations](../modules-and-quasicoherent/quasicoherent-local-presentations.md)

## Proof depends on

- [Affine quasi-coherent equivalence](../modules-and-quasicoherent/affine-quasicoherent-equivalence.md)
- Degree-zero homogeneous localization of graded modules, which is not yet
  packaged in pinned Mathlib.

## Sources

- [Hartshorne II.5, definition and Proposition 5.11 (pp.116–117)](../../../sources/hartshorne-ii-5.md#graded-modules-twists-and-reconstruction-on-proj)
