---
article_id: af_b50502a7621858814a6db862
declaration: definition
origin: cited
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.gradedModuleTwist
---

# Integer-graded module twists

Let `M = ⊕ d : ℤ, M_d` be a graded module over an integer-graded ring. For
`l : ℤ`, define its twist by

`M(l)_d = M_{d+l}`.

The sole main artifact is planned as `Hartshorne.gradedModuleTwist`, carrying
the reindexed direct-sum decomposition and the compatible graded scalar
action. A graded linear equivalence is represented by an ordinary linear
equivalence together with equality of the images of every indexed piece;
supporting lemmas give the identity twist and composition of twists.

Using `ℤ` on both the ring and module sides avoids a truncated subtraction
convention. In particular, if a homogeneous element has degree `l`, the cyclic
module it generates will be graded-equivalent to `(S/p)(-l)`, exactly as in
Hartshorne's proof.

## Depends on

- [The integer grading on a polynomial ring](integer-polynomial-grading.md)

## Sources

- [Hartshorne I.7, definition of the twisted module before Proposition 7.4 (p. 50)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
