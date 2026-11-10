---
article_id: af_3fbc46711bd77afee0c430be
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.ExteriorPowerExactFiltration.exteriorPower_exact_filtration_of_isLocallyFree Hartshorne.ExteriorPowerExactFiltration.exists_exteriorPower_exact_filtration_of_isLocallyFree Hartshorne.ExteriorPowerExactFiltration.exteriorPower_exact_det Hartshorne.ExteriorPowerExactFiltration.filSh Hartshorne.ExteriorPowerExactFiltration.wedgeSheafMap Hartshorne.ExteriorPowerExactFiltration.filSh_eq_imageSubobject
---

# Exterior powers of an exact sequence

For a short exact sequence of locally free sheaves (of arbitrary rank)
$0 \to F' \to F \to F'' \to 0$ and any $r$, the sheaf $\bigwedge^r F$ has a finite
filtration
$\bigwedge^r F = F^0 \supseteq F^1 \supseteq \cdots \supseteq F^r \supseteq F^{r+1} = 0$
with quotients

$F^p/F^{p+1} \cong \bigwedge^p F'\otimes\bigwedge^{r-p}F''$.

In particular, if $F'$, $F$, $F''$ have finite ranks $n'$, $n$, $n''$, then
$\bigwedge^n F \cong \bigwedge^{n'} F' \otimes \bigwedge^{n''} F''$.

As in the source, $F$ is assumed locally free too; the proof does not use this hypothesis.

## Depends on

- [Sheaf tensor, symmetric, and exterior operations](sheaf-tensor-operations.md)
- [Sheaves of modules](../modules-and-quasicoherent/sheaves-of-modules.md)
- [Tensor products of module sheaves](../modules-and-quasicoherent/module-tensor-product.md)
- [Locally free and invertible module sheaves](../modules-and-quasicoherent/locally-free-and-invertible.md)

## Proof depends on

- [Stalkwise exactness](../sheaves/stalkwise-exactness.md)
- [Isomorphisms are detected on stalks](../sheaves/stalkwise-isomorphism.md)
- [Duality for finite locally free sheaves](../modules-and-quasicoherent/finite-locally-free-duality.md)
- Stalks of a locally free sheaf are free, exterior powers and tensor products
  commute with stalks, and the module-level exterior filtration of a split
  exact sequence of free modules of arbitrary rank.
- In finite rank, local splitting of a short exact sequence with locally free
  quotient, used for the top-degree isomorphism.

## Sources

- [Hartshorne II.5, Exercise 5.16(d) (p.128)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
