# Cohomology on an open object

## Prior implementation guidance

For an abelian sheaf `F` on `X`, an open subset `U`, and `i : N`, construct a
natural isomorphism between Mathlib's objectwise site cohomology
`Sheaf.H' F i U` and the degree-`i` cohomology of the restriction `F|_U` on
the topological space `U`.

This is the unique comparison needed to turn `Sheaf.cohomologyPresheaf` into
Hartshorne's presheaf of cohomology on inverse-image opens. The pinned
Mathlib file lists precisely this comparison as TODO, so no upstream status
is asserted. The node remains not ready until the over-site/open-subspace
equivalence and its compatibility with the constant integral sheaf are fixed
as a Lean interface.

## After the sheaf-cohomology split

The cohomology `H^i(U,F|_U)` in the statement is Hartshorne's derived-functor
cohomology (article `sheaf-cohomology`). Passing from Mathlib's Ext-model
`Sheaf.H'` / `Sheaf.H` on `U` to it uses the bridged comparison
`sheaf-cohomology-ext-comparison` (af_20b90b5104320442f4732041), now listed
under Proof depends on. The over-site blocker above is unchanged.

## Restriction of injective abelian sheaves

The direct abelian-sheaf restriction theorem named in the proof outline already exists as
`Hartshorne.injective_openRestrict_obj` (`Hartshorne/Cohomology/CohomologyWithSupports.lean`),
proved from the abelian extension-by-zero adjunction and not recorded on any article. The
article Injectives restrict to open subsets records only the module-sheaf form
(`Hartshorne.injective_moduleSheafRestrict_obj`, abelian sheaves being modules over the
constant sheaf `ℤ`), so it is linked under Informally uses. If the formalization uses the
module form instead, move that link to Proof depends on.
