---
article_id: af_64778191cf786477556c0eb8
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.exists_dedekind_affine_model
---

# Dedekind localizations occur on nonsingular affine curves

Let $k$ be algebraically closed and let $B$ be a finitely generated
$k$-algebra domain which is Dedekind of Krull dimension exactly one.
Let $K$ be a fraction field of $B$, with compatible embeddings
$k\subseteq B\subseteq K$. For every maximal ideal $\mathfrak p$ of $B$,
there are a nonsingular affine curve $Y$, a point $P\in Y$, and compatible
isomorphisms of $k$-algebras

$$e_B:A(Y)\cong B,\qquad e_K:K(Y)\cong K,\qquad
 e_P:\mathcal O_{P,Y}\cong B_{\mathfrak p},$$

with $e_B(\mathfrak m_P)=\mathfrak p$. The isomorphisms commute with
the coordinate-ring and local-ring embeddings into the fraction fields.
Thus for a local germ $z$, its image under $e_K$ is the image of $e_P(z)$
under the canonical inclusion $B_{\mathfrak p}\hookrightarrow K$.

Realize $B$ as a coordinate ring using Hartshorne's Remark I.1.4.6 and
transport $\mathfrak p$ to a point using Theorem I.3.2(b). Dimension makes
$Y$ a curve. Every local ring is a localization of the Dedekind domain,
hence a discrete valuation ring and regular; therefore $Y$ is nonsingular.

## Depends on

- [Curves](../nonsingular-curves/curve.md)
- [Intrinsic nonsingularity](../nonsingular-varieties/intrinsic-nonsingularity.md)

## Proof depends on

- [Every finitely generated domain is a coordinate ring](../affine-varieties/coordinate-ring-realization.md)
- [Dimension is the dimension of the coordinate ring](../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [Points and maximal ideals](../morphisms/points-eq-maximal-ideals.md)
- [The local ring is a localisation](../morphisms/local-ring-is-localization.md)
- [The function field is the fraction field](../morphisms/function-field-is-fraction-field.md)
- [Localizations of a Dedekind domain are DVRs](../nonsingular-curves/dedekind-localization-dvr.md)
- [Characterizations of discrete valuation rings](../nonsingular-curves/dvr-characterizations.md)
- [The function field is the fraction field of every local ring](../nonsingular-curves/local-ring-fraction-field.md)

## Sources

- [Hartshorne I.6, affine curve constructed in Lemma 6.5 and Corollary 6.6 (pp. 41--42)](../../sources/hartshorne.md#i6-normalization-and-finite-poles)
