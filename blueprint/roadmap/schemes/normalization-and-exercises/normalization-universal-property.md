---
article_id: af_2a6303717034db019467c6df
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.absoluteNormalization_existsUnique_lift
---

# The universal property of normalization

If $Z$ is normal and integral and $f : Z \to X$ is dominant, then $f$ factors uniquely through the normalization $\nu : \widetilde{X} \to X$.

Dominance embeds $K(X)$ into $K(Z)$. On affine opens, normality forces every element integral over the image of the target ring to land in the source section ring. Construct compatible local lifts and glue; uniqueness follows from density and separatedness of the affine charts.

## Depends on

- [Construction of the normalization](normalization-construction.md)
- [Normal schemes](normal-scheme.md)

## Proof depends on

- The universal property of integral closure and equality of morphisms on a dense open.
- [Affine opens have fraction field $K(X)$](function-field-integral-scheme.md)

## Sources

- [Hartshorne II.3 (later-used-exercises)](../../../sources/hartshorne-ii-3.md#later-used-exercises)
