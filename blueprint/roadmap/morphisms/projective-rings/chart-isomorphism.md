---
article_id: af_0f2fc7f66b84519f39d31cf5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isIso_chartHom
---

# The charts are isomorphisms of varieties

The chart $\varphi _{i} : U_{i} \to \mathbb{A} ^{n}$ of [Proposition I.2.2](../../projective-varieties/standard-affine-charts.md) is an isomorphism of varieties, not
merely a homeomorphism (Proposition 3.3).

It is proved here in the form $\varphi _{i} : Y_{i} \to \varphi _{i}(Y_{i})$ for a quasi-projective $Y$,
with $Y_{i} = Y \cap U_{i}$; taking $Y = \mathbb{P} ^{n}$ gives Hartshorne's statement. The general
form is not decoration. Hartshorne states 3.3 for the chart and then applies it
to $Y_{i}$ without comment, which is standard practice and is a different theorem;
Theorem 3.4 uses only the version with $Y$ in it. Nothing in the proof changes,
because the two ingredients — that $x_{i}$ is nowhere zero on the chart, and that
dehomogenising inverts the ratio description — are conditions on points of the
chart, and $Y_{i}$ has only fewer of them.

Only the regular functions remain to be checked. On $U_{i}$ they are locally
quotients of homogeneous polynomials of equal degree in $x_{0},\ldots ,x_{n}$; on $\mathbb{A} ^{n}$ they
are locally quotients of polynomials in $y_{1},\ldots ,y_{n}$; and the maps $\alpha$ and $\beta$ from
the proof of [Proposition I.2.2](../../projective-varieties/standard-affine-charts.md) identify the two descriptions.

Small as it is, this node is what transfers Theorem 3.2 to projective varieties.
Without it the chart gives only a homeomorphism, and the counterexamples in
Exercise 3.2 show a homeomorphism carries no information about regular
functions.

## The two directions are checked by different means

Forward is [Lemma I.3.6](../morphism-to-affine-criterion.md), and this is where it repays being stated for an arbitrary
source: the coordinates of $\varphi _{i}$ are $x_j/x_i$, ratios of homogeneous polynomials
of degree one whose denominator is nowhere zero on $U_{i}$ by the definition of the
chart, so the criterion applies with nothing else to check.

Backward is not covered by that lemma, whose target must be affine, so the
pullback of a regular function is checked by hand. A regular function on an open
subset of $U_{i}$ is locally $g/h$ with $g$ and $h$ homogeneous of the same degree,
and $\beta$ turns that into $\alpha (g)/\alpha (h)$, a ratio of polynomials in the affine
coordinates. Two facts make it go through: the ratio of two homogeneous
polynomials of equal degree does not see the choice of representative, and
$\beta (y)$ may be represented by the vector with $1$ in slot $i$, which is exactly
what dehomogenising computes with.

Treating $U_{i}$ as a variety at all needs $\mathbb{P} ^{n}$ to be irreducible; see
[projective and quasi-projective varieties](../../projective-varieties/projective-variety.md).


## Depends on

- [Morphisms](../morphism.md)
- [The standard affine charts](../../projective-varieties/standard-affine-charts.md)
- [Regular functions on a quasi-projective variety](../regular-function-quasi-projective.md)

## Proof depends on

- [Criterion for a morphism into an affine variety](../morphism-to-affine-criterion.md)
- [Varieties are covered by affine pieces](../../projective-varieties/affine-cover.md)

## Sources

- [Hartshorne I.3, Proposition 3.3 (p. 18)](../../../sources/hartshorne.md#i3)
