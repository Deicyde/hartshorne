---
article_id: af_75374f590a194c0db1b7c924
declaration: definition
origin: cited
source_units: [chapter-iii-sections-6-7]
---

# Dualizing sheaves

Let `X` be a proper scheme of dimension `n` over a field `k`. A dualizing
sheaf on `X` consists of a coherent `O_X`-module `ω°_X`, a `k`-linear trace

`tr_X : Hⁿ(X,ω°_X) →ₗ k`,

and the assertion that for every coherent `F`, composition followed by trace
induces a natural linear equivalence

`Hom_X(F,ω°_X) ≃ Dual k (Hⁿ(X,F))`.

The trace is part of the data. This definition neither assumes that `X` is
Cohen–Macaulay nor that `ω°_X` is invertible.

## Depends on

- [Proper morphisms](../../../schemes/proper-and-projective/proper-morphism.md)
- [The affine-local criterion for coherent modules](../../../schemes/modules-and-quasicoherent/coherent-affine-local-criterion.md)
- [Module and abelian-sheaf cohomology agree](../../sheaf-cohomology/module-cohomology-comparison.md)
- [Module sections are representable](../../sheaf-cohomology/module-sections-representable.md)

## Proof depends on

- A coherent-module full subcategory and the contravariant Hom functor into
  `ModuleCat k`.
- The base-field module structure on module-sheaf cohomology.

## Sources

- [Hartshorne III.7, dualizing-sheaf definition, p.241](../../../../sources/hartshorne-iii-7.md#dualizing-sheaves-and-projective-existence-pp241242)
- [Stacks Project, Lemma 48.27.1, tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
