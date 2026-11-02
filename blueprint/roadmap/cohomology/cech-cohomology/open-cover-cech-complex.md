---
article_id: af_12230dca41ee47c4aefe7488
declaration: definition
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.OrderedCechIndex Hartshorne.orderedCechIntersection Hartshorne.orderedCechCochains Hartshorne.orderedCechCoface Hartshorne.orderedCechDifferential Hartshorne.orderedCechComplex Hartshorne.orderedCechCohomology
---

# The ordered Čech complex

For a well-ordered open cover $U = (U_i)$ and an abelian sheaf $F$, define
the cochain complex

$C ^p(U,F) = \prod _{(i_0 < \ldots < i_p)} F(U_i0 \cap \ldots \cap U_{ip})$

with the alternating restriction differential. Define
$\check{H}^p(U,F)$ as its $p$th cohomology.

## Depends on

- [Complexes in an abelian category](../derived-functors/abelian-complexes-and-homotopy.md)
- [Intersections of open sets](../../schemes/sheaves/sheaves-of-abelian-groups.md)

## Proof depends on

- The alternating-face identity gives $d^2=0$.
- The comparison between the ordered Čech complex and the complex retaining all index tuples.

## Sources

- [Hartshorne III.4, definition and Remark 4.0.1 (pp.218–219)](../../../sources/hartshorne-iii-3-4.md#cech-construction-and-comparison)
- [Čech representation choice](../../../sources/hartshorne-iii-3-4.md#project-authored-representation-choices)
