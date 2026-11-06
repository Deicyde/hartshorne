# Quasi-coherent sheaves are filtered unions of coherent subsheaves

## Partial progress

Module `Hartshorne.Cohomology.QuasicoherentCoherentSubobjects` (sorry-free, not
recorded in the article frontmatter) models a coherent subsheaf of `F` as a
subobject of `F` in `X.Modules` whose underlying module is coherent
(`Hartshorne.CoherentSubobject F`, ordered as subobjects). It proves, for `X`
locally Noetherian and `F` quasi-coherent:

- `Hartshorne.isCoherent_kernel_of_isQuasicoherent`,
  `Hartshorne.isCoherent_image_of_isQuasicoherent`: kernel and image of a map
  from a coherent module to a quasi-coherent module are coherent;
- `Hartshorne.coherentSubobject_isFiltered`: the poset is filtered (zero
  subobject; the image of the biproduct bounds two coherent subobjects);
- `Hartshorne.coherentSubobjectDiagram`, `Hartshorne.coherentSubobjectCocone`:
  the diagram of underlying modules and its cocone with vertex `F`.

## Remaining goal

For `X` Noetherian, `Nonempty (IsColimit (coherentSubobjectCocone F))`.

## Missing prerequisite

The colimit statement needs every local section of `F` over an affine open to
lie in a coherent subsheaf of `F` defined on all of `X`. That is the extension
statement of Hartshorne II Ex. 5.15(d), roadmap article
`schemes/coherent-sheaves/coherent-extension` (with
`schemes/coherent-sheaves/coherent-extension-affine` and
`schemes/modules-and-quasicoherent/qcqs-pushforward-quasicoherent` beneath it),
all still unformalized, and not among this article's dependencies. The article's
"Proof depends on" should list `coherent-extension`.

## Next route

1. Grothendieck abelian structure on `X.Modules`: the project proves it
   privately in `Hartshorne.Cohomology.ModuleSheavesEnoughInjectives`; expose it
   as a public instance. It gives `WellPowered`, so `Subobject F` is small.
2. Reindex by a small model (e.g. `Shrink` of `CoherentSubobject F`, or the
   functor to `MonoOver F`) and apply
   `IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup`; that reduces the
   colimit statement to the supremum of the coherent subobjects being `⊤`.
3. Prove the supremum is `⊤` by checking epimorphy on sections over each
   affine open of a finite affine cover: a section `s` over an affine `U`
   generates a coherent subsheaf of `F|_U` (finitely generated submodule
   `A s` of `Γ(U, F)`, then tilde), which extends to a coherent subsheaf of `F`
   by Ex. 5.15(d).
