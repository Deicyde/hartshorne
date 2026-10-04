---
article_id: af_5751579faeac72bcf37aa015
declaration: theorem
origin: cited
source_units: [chapter-v-section-4]
---

# Cubics through at most seven general assigned points have no extra base points

Let plane cubics have ordinary assigned points `P_1,...,P_r`, where `r<=7`, no four
are collinear, and no seven lie on a conic. Then the system has no unassigned
base points.

The same result holds in Hartshorne's stated cases where `P_2` is infinitely
near `P_1`, an inspected base point is infinitely near an assigned point, or
both. These are the named directly-infinitely-near variants; no arbitrary
successive cluster is asserted, and line/conic incidence is tested using
strict transforms on the relevant blowup.

## Depends on

- [Conics through assigned points](conic-assigned-points-system.md)
- [Assigned and unassigned base points](assigned-unassigned-basepoint-api.md)

## Proof depends on

- For any proposed extra point, construct a cubic as a conic plus a joining
  line that avoids it. The three incidence cases use conic uniqueness and the
  no-four/no-seven hypotheses; the infinitely-near versions require the same
  construction with tangent directions.

## Sources

- [Hartshorne V.4, Proposition 4.3, pp.399–400](../../../../sources/hartshorne-v-4.md)
