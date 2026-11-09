---
article_id: af_161a502758e7e12d572005a7
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.planeCurveMultiplicity Hartshorne.planeCurveMultiplicity_pos_iff
---

# Multiplicity of a point on a plane curve

Let $k$ be algebraically closed, let $Y \subseteq \mathbb{A}^2$ be the plane curve
defined by a polynomial $f(x,y)$, and let $P=(a,b)$ be a point of $\mathbb{A}^2$.
Translate $P$ to the origin and expand

$f(x+a,\,y+b)=f_0+f_1+\cdots+f_d$,

where each $f_i$ is a homogeneous polynomial of degree $i$ in $x$ and $y$.  The
*multiplicity* $\mu_P(Y)$ of $P$ on $Y$ is the least $r$ with
$f_r \ne 0$.  Since $f_0=f(P)$, the point $P$ lies on $Y$ if and only if
$\mu_P(Y)>0$.

The multiplicity is computed from the given defining polynomial $f$, as are
the local intersection multiplicities that use it.

## Depends on

- [Algebraic sets](../../affine-varieties/algebraic-set.md)

## Sources

- [Hartshorne I.5, Exercise 5.3 (definition of multiplicity only), p.36](../../../sources/hartshorne.md#i5-exercises-and-exercise-only-prerequisite)
