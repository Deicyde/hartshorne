# Quasi-coherent sheaves are filtered unions of coherent subsheaves

## Lean

The statement is `Hartshorne.isFiltered_coherentSubobject_and_nonempty_isColimit` in module
`Hartshorne.Cohomology.QuasicoherentFilteredUnionCoherent`: for `X` Noetherian and `F`
quasi-coherent, `IsFiltered (CoherentSubobject F)` and the inclusion cocone
`coherentSubobjectCocone F` is a colimit cocone. "Its canonical colimit maps isomorphically to
`F`" is rendered as `IsColimit` of the cocone with vertex `F`, which is equivalent; the index
poset lives in `Type (u + 1)`, so the existence of the colimit object is not assumed separately.

A coherent subsheaf of `F` is a subobject of `F` in `X.Modules` whose underlying module is
coherent (`Hartshorne.CoherentSubobject F`, ordered as subobjects), defined in
`Hartshorne.Cohomology.QuasicoherentCoherentSubobjects` together with:

- `isCoherent_kernel_of_isQuasicoherent`, `isCoherent_image_of_isQuasicoherent` (locally
  Noetherian `X`);
- `coherentSubobject_isFiltered` (filteredness, locally Noetherian `X`);
- `subobjectFamilyDiagram`, `subobjectFamilyCocone`, `coherentSubobjectDiagram`,
  `coherentSubobjectCocone`;
- `nonempty_isColimit_subobjectFamilyCocone` (Grothendieck abelian categories, via Mathlib's
  `IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup`);
- `subobject_eq_top_of_forall_mem_range`,
  `nonempty_isColimit_coherentSubobjectCocone_of_forall_mem` (reduction to: every local section
  lies in a coherent subsheaf).

The new module adds `toModulesι` (the inclusion of a local submodule family, a mono) and
`exists_coherentSubobject_mem_range`: for `s : Γ(F, U)`, take `spanOn U {s}` (sections spanned
by `s` over affine opens in `U`), coherent on `U` by `sub_spanOn_eq` and `extendsOver_spanOn`;
`exists_isCoherent_eq_on_of_isNoetherian` (the core of the coherent-extension article) extends
it to a coherent `N' ⊆ F` agreeing on `U`, so `s ∈ N'(U)`.

## Pending cleanup

The Grothendieck abelian structure of `X.Modules` is a private theorem
(`modules_isGrothendieckAbelian`) in `QuasicoherentCoherentSubobjects`, a copy of the private
`sheafModules_isGrothendieckAbelian` of `Hartshorne.Cohomology.ModuleSheavesEnoughInjectives`
specialised to schemes. Making that one public there (another article's module) and deleting the
copy is a pending cleanup.
