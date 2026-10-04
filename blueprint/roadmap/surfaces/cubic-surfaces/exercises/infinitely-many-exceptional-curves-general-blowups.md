---
article_id: af_1e0776da65772b996afa96a1
declaration: theorem
origin: cited
source_units: [chapter-v-section-4]
---

# At least nine general blowups have infinitely many exceptional curves

Assume the algebraically closed ground field is uncountable. Blow up
`r>=9` points of `P^2` in general position. The resulting surface contains
infinitely many distinct smooth rational curves of self-intersection `-1`.

## Depends on

- [General position is preserved and admits dense extensions](general-position-dense-extension.md)
- [The common blowup model of the quadratic transformation](../assigned-systems/quadratic-transformation-common-blowup.md)
- [Strict transforms under a point blowup](../../monoidal-transformations/strict-transforms/strict-transform-api.md)
- [The exceptional curve has self-intersection minus one](../../monoidal-transformations/foundations/exceptional-curve-self-intersection.md)

## Proof depends on

- For `r=9`, apply suitable sequences of admissible quadratic
  transformations so that the strict transform of the line through the first
  two points remains a smooth rational curve of self-intersection `-1` and
  acquires arbitrarily large plane degree. These unbounded degrees distinguish
  infinitely many such strict transforms on the original blowup.
- For `r>9`, use the dense-extension theorem recursively and choose every
  additional point outside the countable union of the already-produced
  curves. Their strict transforms remain smooth rational `(-1)`-curves, while
  the full point set remains in general position.

## Sources

- [Hartshorne V.4, Exercise 4.15(e), p.409](../../../../sources/hartshorne-v-4.md#exercise-disposition-printed-pp406409)
- [Hartshorne V.5, Remark 5.8.1, p.418](../../../../sources/hartshorne-v-4.md#exercise-disposition-printed-pp406409)
