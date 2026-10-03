---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-6-7]
---

# The top perfect pairing on projective space

For `X=Pⁿ_k` and every coherent `O_X`-module `F`, composition with the
chosen trace gives a perfect pairing of finite-dimensional `k`-vector
spaces

`Hom_X(F,ω_X) × Hⁿ(X,F) ⟶ k`.

Equivalently, the induced map
`Hom_X(F,ω_X) →ₗ Dual k (Hⁿ(X,F))` is a linear equivalence. Perfectness is
recorded with `LinearMap.IsPerfPair`, not merely as nondegeneracy on one side.

## Depends on

- [A trace isomorphism on projective space](projective-space-canonical-trace.md)
- [The affine-local criterion for coherent modules](../../../schemes/modules-and-quasicoherent/coherent-affine-local-criterion.md)
- [Module and abelian-sheaf cohomology agree](../../sheaf-cohomology/module-cohomology-comparison.md)

## Proof depends on

- [The perfect twist pairing](../../projective-cohomology/projective-space-twist-perfect-pairing.md)
- [Finite twisted free covers](../../../schemes/projective-sheaves/finite-twisted-free-cover.md)
- The kernel comparison for two left-exact contravariant functors applied to
  a finite twisted-free presentation.

## Sources

- [Hartshorne III.7, Theorem 7.1(b), p.240](../../../../sources/hartshorne-iii-7.md#duality-on-projective-space-pp239241)
- [Stacks Project, Remark 48.27.2, tag 0FVW](https://stacks.math.columbia.edu/tag/0FVW)
