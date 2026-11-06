---
article_id: af_436941c8814fd3a1df66a43d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.bijective_toValuationSpecData Hartshorne.valuationSpecEquiv Hartshorne.ValuationSpecData Hartshorne.reducedPointClosureStalkToResidueField
---

# Maps from spectra of valuation rings

Let $R$ be a valuation ring with fraction field $K$. A morphism
$\operatorname{Spec} R \longrightarrow X$ is equivalent to a generic point datum consisting of a point
$x_{1} : X$ and an embedding $\kappa (x_{1}) \to K$, together with a specialization
$x_{1} \rightsquigarrow x_{0}$ for which $R$ dominates the image in $K$ of the local ring of
$x_{0}$ on the reduced closed subscheme $\operatorname{closure} \{x_{1}\}$.

The classification of $\operatorname{Spec} K \longrightarrow X$ by a point and a residue-field map is
the existing field-valued-points result and is input to this theorem, not a
second main result of the leaf.

Classify morphisms from the spectrum of a local ring by local
maps from a target stalk. Identify the generic and closed points
of the valuation spectrum and factor through the reduced closure.
Conversely, domination gives the required local map to the
valuation ring and hence its spectrum morphism.

## Depends on

- [Field-valued points of a scheme](../foundational-properties/field-valued-points.md)
- [Specialization and generization](../first-properties/specialization.md)
- [The reduced induced closed subscheme](../subschemes-and-dimension/reduced-induced-closed-subscheme.md)
- [The stalk of an affine scheme](../spectrum-and-schemes/spec-stalk.md)

## Proof depends on

- Morphisms from the spectrum of a local ring are classified by local homomorphisms from the target stalk.
- Identification of the function field of an integral reduced closure with
  the residue field of its generic point.

## Sources

- [Hartshorne II.4, Lemma 4.4](../../../sources/hartshorne-ii-4.md#separatedness-and-the-valuative-criterion)
