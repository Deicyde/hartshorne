---
article_id: af_8d604cc43b75df685cf8ce8e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.tensorPullbackTilde Hartshorne.cohomologyTensor Hartshorne.cohomologyTensorδ Hartshorne.IsCovariantDeltaFunctor Hartshorne.tensorPullbackTilde_shortExact Hartshorne.cohomologyTensor_isCovariantDeltaFunctor Hartshorne.cohomologyTensorModule Hartshorne.cohomologyTensorModuleδ Hartshorne.cohomologyTensorModule_comp_forget₂ Hartshorne.forget₂_map_cohomologyTensorModuleδ Hartshorne.cohomologyTensorModule_isCovariantDeltaFunctor
---

# Cohomology after tensor is a delta functor

Let $A$ be Noetherian, $Y = \operatorname{Spec} A$, $f : X \to Y$ projective, and $F$ a
coherent $\mathcal{O}_X$-module flat over $Y$. For an $A$-module $M$, set

$T^i(M) = H^i(X, F \otimes _A M)$.

Here $M$ is first associated to a quasicoherent module on $Y$, pulled back to
$X$, and tensored with $F$. Each $T^i$ is additive and covariant, every short
exact sequence of $A$-modules gives the natural long exact cohomology
sequence, and the collection $(T^i)_{(i \ge 0)}$ is a covariant delta functor.
In particular, every $T^i$ is exact in the middle.

The Noetherian, projectivity and coherence hypotheses are kept as in the
source; they are not needed here, because only the flatness of $F$ over $Y$
enters the argument.

## Depends on

- [A module sheaf flat over a base](../../flat-families/flatness/module-sheaf-flat-over-base.md)
- [Tensor products of module sheaves](../../../schemes/modules-and-quasicoherent/module-tensor-product.md)
- [The affine quasicoherent equivalence](../../../schemes/modules-and-quasicoherent/affine-quasicoherent-equivalence.md)
- [The long exact sequence of right-derived functors](../../derived-functors/right-derived-long-exact-sequence.md)
- [Projective morphisms](../../../schemes/proper-and-projective/projective-morphism.md)
- [The affine-local criterion for coherence](../../../schemes/modules-and-quasicoherent/coherent-affine-local-criterion.md)

## Proof depends on

- Flatness of $F$ over $Y$ makes tensoring the associated short exact sequence
  of module sheaves exact.

## Sources

- [Hartshorne III.12, Proposition 12.1, p.282](../../../../sources/hartshorne-iii-11-12.md#cohomology-after-tensor-and-finite-free-models-pp281287)
