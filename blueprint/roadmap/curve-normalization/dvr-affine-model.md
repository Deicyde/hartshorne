---
article_id: af_99c0d90cb858f171e4e80de6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.FunctionFieldDVR.exists_nonsingular_affine_model
---

# Every function-field DVR has a nonsingular affine model

Let $k$ be algebraically closed, let $K/k$ be a finitely generated field
extension of transcendence degree one, and let $R\in C_K$. There are a
nonsingular affine curve $Y$, a point $P\in Y$, and compatible isomorphisms

$$e_K:K(Y)\cong K,\qquad e_R:\mathcal O_{P,Y}\cong R.$$

The isomorphisms are over $k$ and commute with the embeddings of the local
rings into the function fields. For every germ $z$, the image of $z$ in
$K(Y)$ is carried by $e_K$ to the image of $e_R(z)$ in $K$.

This is Hartshorne's Corollary I.6.6. Choose a separating parameter $t$.
The valuation-ring property says that $R$ contains $t$ or $t^{-1}$.
The corresponding Dedekind normalization chart has a maximal centre at
$R$, and localization at that centre is $R$. The affine-model theorem
realizes this localization as the local ring of a nonsingular curve point.
The compatibility is used to compare residue maps in Proposition I.6.7.

## Depends on

- [Discrete valuation rings of a function field](function-field-dvrs.md)
- [Curves](../nonsingular-curves/curve.md)
- [Intrinsic nonsingularity](../nonsingular-varieties/intrinsic-nonsingularity.md)

## Proof depends on

- [The two separable normalization charts](separable-normalization-charts.md)
- [A DVR containing a Dedekind subring is its localization](dedekind-subring-localization.md)
- [Dedekind localizations occur on nonsingular affine curves](dedekind-affine-model.md)

## Sources

- [Hartshorne I.6, Corollary 6.6 (p. 42)](../../sources/hartshorne.md#i6-normalization-and-finite-poles)
