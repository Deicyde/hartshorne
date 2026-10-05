---
article_id: af_c6ff9d0799602be5f5795566
declaration: definition
origin: cited
source_units: [chapter-iii-sections-8-9]
statement: formalized
proof: formalized
lean: Hartshorne.abelianHigherDirectImage Hartshorne.abelianHigherDirectImageZeroIso
---

# Higher direct images of abelian sheaves

For a continuous map `f : X -> Y` and `i : N`, define the higher direct
image functor on abelian sheaves by

`R^i f_* = (TopCat.Sheaf.pushforward AddCommGrpCat f).rightDerived i`.

The degree-zero comparison identifies `R^0 f_*` naturally with ordinary
direct image. The pinned declarations `TopCat.Sheaf.pushforward`,
`Functor.rightDerived`, and `Functor.rightDerivedZeroIsoSelf` are exact prior
art, but their specialization and packaged higher-direct-image interface are
not yet in Mathlib.

## Depends on

- [Abelian-sheaf pushforward is left exact](abelian-pushforward-left-exact.md)
- [Right derived functors](../derived-functors/right-derived-functors.md)
- [Abelian sheaves have enough injectives](../sheaf-cohomology/abelian-sheaves-enough-injectives.md)
- [Direct image of a sheaf](../../schemes/sheaf-functors/direct-image.md)

## Sources

- [Hartshorne III.8, definition, printed p.250](../../../sources/hartshorne-iii-8.md#definition-and-local-description-printed-pp-250251)
