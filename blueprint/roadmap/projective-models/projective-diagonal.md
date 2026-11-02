---
article_id: af_7573872cfdef047cd2572bae
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.ValuationSpace.exists_dense_projective_diagonal
---

# The projective diagonal model

The extended morphisms $\varphi_0,\varphi_1$ give a diagonal map
$C_K\to Y_0\times Y_1$ into the Segre product. Its image closure is an
irreducible projective variety $Y$, and the diagonal induces a dense morphism
$\varphi:C_K\to Y$.

This is Hartshorne's product-and-closure construction for the two
normalization charts. It retains the chart identifications and the
projection identities

$$\pi_i\circ\varphi=\varphi_i\qquad(i=0,1).$$

The function-field and local-ring comparisons use this same diagonal,
projective model, and chart identifications.

## Depends on

- [Extensions to the projective chart closures](projective-chart-extensions.md)
- [Products of varieties](../rational-maps/product-variety.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)
- [Morphisms](../morphisms/morphism.md)

## Sources

- [Hartshorne I.6, construction in the proof of Theorem 6.9 (pp. 44--45)](../../sources/hartshorne.md#i6-projective-models)
