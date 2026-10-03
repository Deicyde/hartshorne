# Coherent sheaves, ideals, and support

This milestone covers the ideal-sheaf consequences of Hartshorne II.5 and the
adopted coherence exercises: support, stalkwise local freeness, and extension
from an open subset. It depends on the affine quasi-coherent and coherent
machinery in the sibling `modules-and-quasicoherent` chapter.

Mathlib's `IdealSheafData` is compatible affine-open ideal data, not literally
a subobject in `X.Modules`. The first two leaves deliberately bridge those
representations before using the existing closed-subscheme equivalence.

- [Ideal sheaves of closed immersions](closed-immersion-ideal-sheaf.md)
- [Module ideal sheaves and ideal data](module-ideal-sheaf-data.md)
- [Closed subschemes and ideal data](closed-subschemes-ideal-data.md)
- [Support of a quasi-coherent module](module-sheaf-support.md)
- [Affine sections with support](affine-sections-with-support.md)
- [Quasi-coherence of sections with support](sections-with-support-quasicoherent.md)
- [The free locus of a coherent sheaf](coherent-free-locus.md)
- [Affine extension of coherent sheaves](coherent-extension-affine.md)
- [Extension of coherent sheaves](coherent-extension.md)
- [Closed immersions are finite](closed-immersion-finite.md)

## Sources

- [Hartshorne II.5 source notes](../../../sources/hartshorne-ii-5.md)
