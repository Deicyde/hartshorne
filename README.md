# Hartshorne, Algebraic Geometry

A Lean 4 formalization of the classical variety theory in Chapter I of Robin
Hartshorne, *Algebraic Geometry* (Springer, Graduate Texts in Mathematics 52,
1977), built on Mathlib.

Sections I.1 through I.3 are decomposed into a dependency graph of 54
formalization targets, from the definition of an algebraic set to Corollary
I.3.8: the functor sending an affine variety to its coordinate ring is an
arrow-reversing equivalence onto the finitely generated integral domains over
`k`. Sections I.4 onward and Chapters II through V are out of scope; see the
[coverage contract](blueprint/coverage/README.md) for exactly what is and is not
claimed.

**46 of the 54 targets are done**: 45 proved here, sorry-free and depending only
on Lean's three standard axioms, and one already in Mathlib. Among them are the
Nullstellensatz correspondence, irreducible decomposition, the projective
Nullstellensatz and the standard affine charts, regular functions and the
identity principle, morphisms of varieties, the local ring at a point with its
`IsLocalRing` instance, Theorem 1.8A(a), Theorem 3.2(a) and (b), Lemma 3.6,
Proposition 3.5, Corollary 3.7, and Corollary 3.8 itself, the destination of the
whole chapter: the coordinate ring functor is an arrow-reversing equivalence
onto the finitely generated integral domains.

Eight remain. The one that blocks the most is the second clause of Theorem
1.8A, the dimension formula `height 𝔭 + dim B/𝔭 = dim B`, which Hartshorne
quotes from Matsumura and which the pinned Mathlib has in no form.

**Site:** <https://deicyde.github.io/hartshorne/>

[Browse the formalization blueprint](blueprint/README.md).

Built with Lean 4 `v4.33.1` and Mathlib `v4.33.1`.

Developed with [AutoformBot](https://github.com/facebookresearch/autoform-bot).
