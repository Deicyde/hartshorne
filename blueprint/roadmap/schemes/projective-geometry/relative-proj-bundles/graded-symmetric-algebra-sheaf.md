---
article_id: af_bd43637b64a7306880f81a2d
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.Modules.symmetricAlgebra AlgebraicGeometry.Scheme.Modules.symmetricAlgebraStructure AlgebraicGeometry.Scheme.Modules.symmetricPower AlgebraicGeometry.Scheme.Modules.symmetricAlgebra_graded AlgebraicGeometry.Scheme.Modules.symmetricAlgebra_isQuasicoherent AlgebraicGeometry.Scheme.Modules.symmetricPower_isQuasicoherent AlgebraicGeometry.Scheme.Modules.symmetricPower_isCoherent AlgebraicGeometry.Scheme.Modules.symmetricPower_isLocallyFree AlgebraicGeometry.Scheme.Modules.symmetricPower_isLocallyFreeOfRank AlgebraicGeometry.Scheme.Modules.symmetricPowerOneIso Hartshorne.moduleSheafSymmetricPowerOneIso Hartshorne.moduleSheafTensorToSymmetricPower Hartshorne.epi_moduleSheafTensorToSymmetricPower Hartshorne.moduleSheafTensorToSymmetricPower_multilinear Hartshorne.moduleSheafTensorToSymmetricAlgebra Hartshorne.epi_moduleSheafTensorToSymmetricAlgebra Hartshorne.moduleSheafTensorAlgebraι_comp_toSymmetricAlgebra Hartshorne.moduleSheafTensorToSymmetricAlgebra_mul Hartshorne.moduleSheafTensorToSymmetricAlgebra_one Hartshorne.SheafTensorOperations.symmetricMonomial_bijective Hartshorne.SheafTensorOperations.MonotoneWord.card Hartshorne.Ringed.IsLocalFrame.moduleSheafSymmetricPower Hartshorne.Ringed.IsLocallyFreeOfRank.moduleSheafSymmetricPower Hartshorne.Ringed.IsFiniteLocallyFree.moduleSheafSymmetricPower Hartshorne.Ringed.IsFiniteLocallyFree.isFinitePresentation Hartshorne.Ringed.IsFiniteLocallyFree.isQuasicoherent_moduleSheafSymmetricAlgebra Hartshorne.polynomialAlgebraSheaf Hartshorne.polynomialAlgebraSheafStructure Hartshorne.polynomialAlgebraSymmetricAlgebraIso Hartshorne.polynomialAlgebraSymmetricAlgebraIso_mul Hartshorne.polynomialAlgebraSymmetricAlgebraIso_one Hartshorne.polynomialAlgebraSymmetricAlgebraIso_X Hartshorne.exists_polynomialAlgebraSheaf_iso_symmetricAlgebra
---

# The graded symmetric-algebra sheaf

For a Noetherian scheme $X$ and a finite locally free $\mathcal{O}_X$-module $E$,
construct the quasi-coherent graded algebra
$\operatorname{Sym}(E)=\bigoplus_d\operatorname{Sym}^d(E)$, generated in degree one, and identify it
locally with a polynomial algebra when $E$ is free. Its degree-one term and
all homogeneous pieces are coherent.

## Depends on

- [Sheaf tensor, symmetric, and exterior operations](../../module-exercises/sheaf-tensor-operations.md)
- [Locally free and invertible module sheaves](../../modules-and-quasicoherent/locally-free-and-invertible.md)
- [Duality for finite locally free sheaves](../../modules-and-quasicoherent/finite-locally-free-duality.md)

## Proof depends on

- The universal property of the symmetric algebra and its polynomial-algebra description on affine trivializations.

## Sources

- [Hartshorne II.7, projective-bundle definition (p.162)](../../../../sources/hartshorne-ii-7.md#relative-proj-and-projective-bundles)
