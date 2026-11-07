---
article_id: af_5ffc461f2f07008cebf36805
declaration: definition
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.affineLocalIntersectionMultiplicity Hartshorne.planeCurveMultiplicity Hartshorne.affineLocalIntersectionMultiplicity_ne_top_and_ge Hartshorne.finite_lines_affineLocalIntersectionMultiplicity_ne Hartshorne.projectivePlaneLocalIntersectionMultiplicity Hartshorne.finite_and_finsum_projectivePlaneLocalIntersectionMultiplicity
---

# Local intersection multiplicity of plane curves

For distinct affine plane curves $Y=(f=0)$ and $Z=(g=0)$ and a point
$P \in Y \cap Z$, define

$(Y\cdot Z)_P=\operatorname{length}_{\mathcal O_{\mathbb A^2,P}}(\mathcal O_{\mathbb A^2,P}/(f,g))$.

This length is finite and at least
$\operatorname{mult}_P(Y)\operatorname{mult}_P(Z)$. For all but finitely many lines $L$ through $P$,
$(L\cdot Y)_P=\operatorname{mult}_P(Y)$. Finally, for a projective plane curve $Y$ of degree
$d$ and a line $L$ not contained in $Y$,

$\sum_{P\in L\cap Y}(L\cdot Y)_P=d$.

The local length is the definition; these three properties are
needed by tangent lines and flex calculations.

The hypotheses that $P$ lies on $Y$ and $Z$ in the first statement and on $Y$ in the second, and the irreducibility of $Y$ in the last, are kept as in the source but are not needed: the statements hold for every point $P$ and, in the last, for every form of degree $d$ not vanishing identically on $L$, with all lengths and multiplicities computed from the given defining polynomials (so for a non-reduced form such as $G^2$ the count is $2\deg G$, not $\deg G$).

## Depends on

- [Bezout's theorem for distinct plane curves](../../intersections-projective-space/bezout/plane-curve-bezout.md)

## Proof depends on

- Parameter ideals in the regular local ring of the affine plane have finite
  colength.
- The initial homogeneous forms control the length lower bound and the
  exceptional tangent directions.
- The local length agrees with the homogeneous-coordinate intersection
  multiplicity used by Bezout.

## Sources

- [Hartshorne I.5, Exercise 5.4, p.36](../../../sources/hartshorne.md#i7-local-multiplicity-comparison-adopted-for-chapter-iv)
