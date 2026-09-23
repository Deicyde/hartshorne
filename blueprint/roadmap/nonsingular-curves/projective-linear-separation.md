---
article_id: af_53cc18015910ca620822fa44
declaration: lemma
origin: bridged
source_units: [chapter-i-section-6-local-structure]
statement: formalized
proof: formalized
lean: Hartshorne.exists_linear_forms_separating_projective_points
---

# Linear fractions separate projective points

Let `P ≠ Q` be points of projective space over the algebraically closed field
`k`. There are degree-one homogeneous polynomials `g` and `h` such that

`g(P) ≠ 0`, `g(Q) ≠ 0`, `h(P) = 0`, and `h(Q) ≠ 0`.

Thus the homogeneous fraction `g/h` is regular at `Q` but has a genuine pole at
`P`. Construct `h` as a linear form separating the two projective lines, then
construct a second linear form with the opposite vanishing pattern and add the
two forms to obtain `g`. The argument works over every field.

This is the projective-coordinate content of Hartshorne's preliminary linear
change of coordinates in Lemma 6.4, isolated so the local-ring argument does
not need a general projective automorphism API.

## Depends on

- [Projective space](../projective-varieties/projective-space.md)

## Sources

- [Hartshorne I.6, proof of Lemma 6.4 (p. 41)](../../sources/hartshorne.md#i6-local-structure-and-point-separation)
