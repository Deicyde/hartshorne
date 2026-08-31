# Hartshorne, Algebraic Geometry

A Lean 4 formalization of the classical variety theory in Chapter I of Robin
Hartshorne, *Algebraic Geometry* (Springer, Graduate Texts in Mathematics 52,
1977), built on Mathlib.

Sections I.1 through I.3 are decomposed into a dependency graph of 47
formalization targets, from the definition of an algebraic set to Corollary
I.3.8: the functor sending an affine variety to its coordinate ring is an
arrow-reversing equivalence onto the finitely generated integral domains over
`k`. Sections I.4 onward and Chapters II through V are out of scope; see the
[coverage contract](blueprint/coverage/README.md) for exactly what is and is not
claimed.

**No results are proved yet.** The roadmap is written; the Lean is not.

**Site:** <https://deicyde.github.io/hartshorne/>

[Browse the formalization blueprint](blueprint/README.md).

Built with Lean 4 `v4.33.1` and Mathlib `v4.33.1`.

Developed with [AutoformBot](https://github.com/facebookresearch/autoform-bot).
