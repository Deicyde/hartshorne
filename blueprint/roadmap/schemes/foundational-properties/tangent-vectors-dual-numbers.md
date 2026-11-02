---
article_id: af_a4a0543ea6d3bb728811d630
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.dualNumberLiftToTangent_bijective
---

# Tangent vectors and the dual numbers

Let $X$ be a scheme over a field $k$, and let $x \in X$ be $k$-rational.  If
$D = k[\varepsilon ]/(\varepsilon ^{2})$, then $k$-morphisms $\operatorname{Spec} D \to X$ whose closed point maps to
$x$ correspond bijectively to the Zariski tangent space

$T_{xX} = \operatorname{Hom} _k(\mathfrak{m} _x/\mathfrak{m} _x^{2}, k)$.

Fix the residue-field map at $x$. Local homomorphisms
$\mathcal{O}_{X,x}\to D$ reducing to it correspond to
$k$-derivations into $k$. Such derivations vanish on
$\mathfrak m_x^2$, so they correspond to linear maps from
$\mathfrak m_x/\mathfrak m_x^2$. Conversely, a linear functional
determines the coefficient of $\varepsilon$.

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)
- [Schemes over a base](../spectrum-and-schemes/over-base.md)

## Proof depends on

- [Field-valued points of a scheme](field-valued-points.md)

## Sources

- [Hartshorne II.2, Exercise 2.8, used in deformation theory and smoothness (p. 80)](../../../sources/hartshorne-ii-2.md#exercises-21-through-29)
