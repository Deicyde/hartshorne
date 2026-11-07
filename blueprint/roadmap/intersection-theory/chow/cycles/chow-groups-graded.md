---
article_id: af_2e3f234e38bdd94f0004e982
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.chowGroup Hartshorne.gradedChowGroup Hartshorne.chowGroupZeroEquivInt Hartshorne.chowGroupZeroEquivInt_mk Hartshorne.subsingleton_chowGroup_of_lt
---

# The graded Chow groups

Define

$A^r(X)=\mathbb{Z}^r(X)/\operatorname{Rat}^r(X)$

and $A(X)=\bigoplus_{r=0}^{\dim X}A^r(X)$. For an integral variety,
$A^0(X)=\mathbb{Z}$, and $A^r(X)=0$ when $r>\dim X$.

At this stage $A(X)$ is a graded abelian group. Its Chow-ring multiplication
is supplied only after constructing the intersection product.

## Depends on

- [Codimension cycles](codimension-cycle-group.md)
- [Rational equivalence via divisors on normalizations](rational-equivalence-via-normalizations.md)
- [Dimension of a scheme](../../../schemes/subschemes-and-dimension/scheme-dimension.md)

## Sources

- [Hartshorne Appendix A.1, Chow-group definition, p.426](../../../../sources/hartshorne-appendix-a-1-2.md)
