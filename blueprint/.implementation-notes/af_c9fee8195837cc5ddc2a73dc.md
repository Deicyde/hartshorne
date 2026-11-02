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
