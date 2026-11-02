---
article_id: af_53cc18015910ca620822fa44
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.exists_linear_forms_separating_projective_points
---

# Linear fractions separate projective points

Let $P\ne Q$ be points of projective space over the algebraically closed
field $k$. There are degree-one homogeneous polynomials $g$ and $h$ such that

$$g(P)\ne 0,\qquad g(Q)\ne 0,\qquad h(P)=0,\qquad h(Q)\ne 0.$$

Thus the homogeneous fraction $g/h$ is regular at $Q$ but has a pole at $P$.
Choose $h$ as a linear form separating the two projective lines. Choose a
second linear form with the opposite vanishing pattern, then add the two
forms to obtain $g$. The argument works over every field.

This is the projective-coordinate step in Hartshorne's preliminary linear
change of coordinates in the proof of Lemma 6.4.

## Depends on

- [Projective space](../projective-varieties/projective-space.md)

## Sources

- [Hartshorne I.6, proof of Lemma 6.4 (p. 41)](../../sources/hartshorne.md#i6-local-structure-and-point-separation)
