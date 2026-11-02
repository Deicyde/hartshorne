---
article_id: af_14eaa7de868a5c79cf51f1a0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.IsQuasiProjVariety.eq_of_localRingRange_le
---

# The local ring determines the point

Let $Y$ be a quasi-projective variety and let $P,Q\in Y$. Regard both local
rings as subalgebras of $K(Y)$ through their canonical injections. Then

$$\mathcal{O}_{Q,Y}\subseteq\mathcal{O}_{P,Y}\quad\Longrightarrow\quad P=Q.$$

This is Lemma 6.4. If $P\ne Q$, choose linear forms $g,h$ with
$g(P)\ne 0$, $g(Q)\ne 0$, $h(P)=0$, and $h(Q)\ne 0$. The class $[g/h]$
belongs to $\mathcal{O}_{Q,Y}$ but not to $\mathcal{O}_{P,Y}$, contradicting
the assumed inclusion.

Hartshorne reaches the same contradiction by moving both points into a
common affine chart and comparing their localizations.

## Depends on

- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)
- [Global regular functions are the intersection of the local rings](../morphisms/global-functions/global-regular-intersection-local-rings.md)

## Proof depends on

- [Linear fractions separate projective points](projective-linear-separation.md)
- [Membership of a homogeneous fraction in a local ring](homogeneous-fraction-local-membership.md)

## Sources

- [Hartshorne I.6, Lemma 6.4 (p. 41)](../../sources/hartshorne.md#i6-local-structure-and-point-separation)
