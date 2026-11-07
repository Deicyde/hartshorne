---
article_id: af_3fbc46711bd77afee0c430be
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.ExteriorPowerExactFiltration.exteriorPower_exact_filtration Hartshorne.ExteriorPowerExactFiltration.exists_exteriorPower_exact_filtration Hartshorne.ExteriorPowerExactFiltration.exteriorPower_exact_det Hartshorne.ExteriorPowerExactFiltration.filSh Hartshorne.ExteriorPowerExactFiltration.wedgeSheafMap Hartshorne.ExteriorPowerExactFiltration.filSh_eq_imageSubobject
---

# Exterior powers of an exact sequence

For a short exact sequence of finite locally free sheaves
$0 \to F' \to F \to F'' \to 0$, the sheaf $\bigwedge^r F$ has the standard finite
filtration whose graded pieces are

$\bigwedge^p F'\otimes\bigwedge^{r-p}F''$.

In top degree this gives
$\det F \cong \det F' \otimes \det F''$.

As in the source, $F$ is assumed locally free too, although this follows from the
hypotheses on $F'$ and $F''$.

## Depends on

- [Sheaf tensor, symmetric, and exterior operations](sheaf-tensor-operations.md)
- [Sheaves of modules](../modules-and-quasicoherent/sheaves-of-modules.md)
- [Tensor products of module sheaves](../modules-and-quasicoherent/module-tensor-product.md)
- [Locally free and invertible module sheaves](../modules-and-quasicoherent/locally-free-and-invertible.md)
- [Duality for finite locally free sheaves](../modules-and-quasicoherent/finite-locally-free-duality.md)

## Proof depends on

- [Stalkwise exactness](../sheaves/stalkwise-exactness.md)
- Local splitting of a short exact sequence with locally free quotient and
  the module-level exterior filtration.

## Sources

- [Hartshorne II.5, Exercise 5.16(d) (p.128)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
