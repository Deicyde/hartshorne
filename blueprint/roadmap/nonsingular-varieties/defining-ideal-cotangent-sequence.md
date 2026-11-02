---
article_id: af_0501b46f3624fa99b6ff84e1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.definingIdealCotangentEquiv_nonempty Hartshorne.residueField_smul_cotangentSpace_eq_baseField_smul Hartshorne.definingIdealGradient_apply Hartshorne.affineCoordinatesToLocalCotangent_surjective Hartshorne.affineCoordinatesToLocalCotangent_ker Hartshorne.finrank_localCotangent_add_finrank_gradientSpace
---

# The defining ideal and the local cotangent space

Let $Y\subseteq\mathbb A^n$ be an affine variety, let $P\in Y$, and
write $\mathfrak b=I(Y)$ and $\mathfrak n_P$ for the ambient polynomial
ring's maximal ideal at $P$. If $\mathfrak m$ is the maximal ideal of
$\mathcal O_{P,Y}$, the identification of its residue field with $k$ gives

$$\mathfrak m/\mathfrak m^2\cong
\mathfrak n_P/(\mathfrak b+\mathfrak n_P^2)$$

as $k$-vector spaces. Combining this with the ambient derivative map gives

$$\dim_k(\mathfrak m/\mathfrak m^2)+
\dim_k\operatorname{span}\{\nabla f(P):f\in I(Y)\}=n.$$

This is the dimension count in Hartshorne's proof of Theorem I.5.1.
The identifications commute with the residue-field maps, preserving the
scalar structure used in this dimension calculation.

## Depends on

- [The cotangent space of affine space](ambient-cotangent-space.md)
- [The local ring is local](../morphisms/local-ring-is-local.md)
- [The local ring is a localisation](../morphisms/local-ring-is-localization.md)
- [Points and maximal ideals](../morphisms/points-eq-maximal-ideals.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Sources

- [Hartshorne I.5, proof of Theorem 5.1 (p. 32)](../../sources/hartshorne.md#i5)
