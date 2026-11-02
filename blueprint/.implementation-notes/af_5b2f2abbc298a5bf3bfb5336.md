# Support of a quasi-coherent module

## Prior implementation guidance

Define the support of `F : X.Modules` by
`Supp(F) = {x | F_x is nonzero}`. If `X = Spec A` and `F = M~`, this set is
`Module.support A M`. Consequently, for finite `M`,
`Supp(M~) = V(ann_A M)`, and the support of a coherent sheaf on a Noetherian
scheme is closed.

## Supporting implementation references

- `Module.mem_support_iff_exists_annihilator`
- `Module.support_eq_zeroLocus`
- `Module.isClosed_support`
