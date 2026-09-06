# Hartshorne, Algebraic Geometry

A Lean 4 formalization of the classical variety theory in Chapter I of Robin
Hartshorne, *Algebraic Geometry* (Springer, Graduate Texts in Mathematics 52,
1977), built on Mathlib.

Sections I.1 through I.3 are decomposed into a dependency graph of 68
formalization targets, from the definition of an algebraic set to Corollary
I.3.8: the functor sending an affine variety to its coordinate ring is an
arrow-reversing equivalence onto the finitely generated integral domains over
`k`. Sections I.4 onward and Chapters II through V are out of scope; see the
[coverage contract](blueprint/coverage/README.md) for exactly what is and is not
claimed.

**All 68 targets are done**: 67 proved here, sorry-free and depending only on
Lean's three standard axioms, and one already in Mathlib. Among them are the
Nullstellensatz correspondence, irreducible decomposition, the dimension of a
variety as the Krull dimension of its coordinate ring, both clauses of Theorem
1.8A including the dimension formula `height 𝔭 + dim B/𝔭 = dim B` that
Hartshorne quotes from Matsumura and that the pinned Mathlib has in no form,
Proposition 1.10 and Proposition 1.13, the projective Nullstellensatz and the
standard affine charts, `dim ℙⁿ = n` and `dim S(Y) = dim Y + 1`, regular
functions and the identity principle, morphisms of varieties, the local ring at
a point with its `IsLocalRing` instance and its dimension, all four parts of
Theorem 3.2, all three parts of Theorem 3.4, and Corollary 3.8 itself, the
destination of the whole chapter: the coordinate ring functor is an
arrow-reversing equivalence onto the finitely generated integral domains.

**Site:** <https://deicyde.github.io/hartshorne/>

[Browse the formalization blueprint](blueprint/README.md).

Built with Lean 4 `v4.33.1` and Mathlib `v4.33.1`.

Developed with [AutoformBot](https://github.com/facebookresearch/autoform-bot).
