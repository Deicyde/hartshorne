# Hartshorne, Algebraic Geometry

A Lean 4 formalization of the classical variety theory in Chapter I of Robin
Hartshorne, *Algebraic Geometry* (Springer, Graduate Texts in Mathematics 52,
1977), built on Mathlib.

Sections I.1 through I.4 are decomposed into a dependency graph of 86
formalization targets, from the definition of an algebraic set through the
blow-up construction following Proposition I.4.9. Sections I.5 onward and
Chapters II through V are out of scope; see the
[coverage contract](blueprint/coverage/README.md) for exactly what is and is not
claimed.

**§§I.1–I.4 are complete.** Of their 86 targets, 85 are proved here,
sorry-free and depending only on Lean's three standard axioms, and one is
already in Mathlib. Completed results include the
Nullstellensatz correspondence, irreducible decomposition, the dimension of a
variety as the Krull dimension of its coordinate ring, both clauses of Theorem
1.8A including the dimension formula `height 𝔭 + dim B/𝔭 = dim B` that
Hartshorne quotes from Matsumura and that the pinned Mathlib has in no form,
Proposition 1.10 and Proposition 1.13, the projective Nullstellensatz and the
standard affine charts, `dim ℙⁿ = n` and `dim S(Y) = dim Y + 1`, regular
functions and the identity principle, morphisms of varieties, the local ring at
a point with its `IsLocalRing` instance and its dimension, all four parts of
Theorem 3.2, all three parts of Theorem 3.4, Corollary 3.8, rational maps and
their composition, the function-field classification up to birational
equivalence, the hypersurface normal form, and blowing up a point.

**Site:** <https://deicyde.github.io/hartshorne/>

[Browse the formalization blueprint](blueprint/README.md).

Built with Lean 4 `v4.33.1` and Mathlib `v4.33.1`.

Developed with [AutoformBot](https://github.com/facebookresearch/autoform-bot).
