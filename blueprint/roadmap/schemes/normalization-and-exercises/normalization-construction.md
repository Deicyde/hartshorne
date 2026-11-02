---
article_id: af_47c3f0f84fedd5df49585e9c
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.absoluteNormalizationGenericMap Hartshorne.absoluteNormalization Hartshorne.absoluteNormalizationMap Hartshorne.absoluteNormalizationOpenCover Hartshorne.absoluteNormalizationObjIso
---

# Construction of the normalization

For an integral scheme $X$, glue $\operatorname{Spec} \overline{A}$ over affine opens $\operatorname{Spec} A$, where $\overline{A}$ is the integral closure of $A$ in $K(X)$, to obtain a morphism $\nu : \widetilde{X} \to X$.

Show integral closure commutes with the localizations representing principal opens. These canonical identifications satisfy the cocycle condition, so the affine normalizations glue together and their maps to $X$ glue to $\nu$.

On each affine open, take the integral closure of its coordinate
ring in the function field. Localization compatibility allows
these affine schemes to glue to the normalization.

## Depends on

- [Normal schemes](normal-scheme.md)
- [The function field of an integral scheme](function-field-integral-scheme.md)
- [Gluing schemes](../spectrum-and-schemes/gluing.md)

## Proof depends on

- Integral closure commutes with localization inside a common fraction field.
- Normalization on affine charts is given by integral closure, compatible with restriction.

## Sources

- [Hartshorne II.3 (later-used-exercises)](../../../sources/hartshorne-ii-3.md#later-used-exercises)
