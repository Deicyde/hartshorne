# Hartshorne, Algebraic Geometry

A Lean 4 formalization of the classical variety theory in Chapter I of Robin
Hartshorne, *Algebraic Geometry* (Springer, Graduate Texts in Mathematics 52,
1977), built on Mathlib.

Sections I.1 through I.4, the geometric core of I.5 through Theorem I.5.3, and
I.6 through Proposition I.6.7 are decomposed into a dependency graph of 138
formalization targets. The completion, Cohen-structure, and analytic-isomorphism
material later in §I.5 is deferred; so is the projective-model material from
Proposition I.6.8 onward. The unadopted exercises, §I.7 onward, and Chapters II
through V are out of scope. See the
[coverage contract](blueprint/coverage/README.md) for exactly what is and is not
claimed.

**The first 114 targets, through Lemma I.6.4, are complete.** Of the first 86
targets in §§I.1–I.4, 85 are proved here,
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

The geometric core of §I.5 contributes 16 further roadmap leaves. Its
regular-local/cotangent-space criterion is an exact Mathlib result and the
other 15 are proved here, culminating in the properness and closedness of the
singular locus. Thus all 102 roadmap leaves are complete: 100 are proved in
this project and two are supplied by Mathlib.

The §I.6 opening adds 12 leaves: two clauses of Theorem 6.1A already in Mathlib
and ten project targets leading to DVR local rings for nonsingular curves and
Lemma 6.4, that the local ring determines the point. All 12 are complete. The
completed 114-leaf portion therefore consists of 110 targets formalized here
and four supplied by Mathlib.

The next 24 planned leaves cover the exact nonseparable integral-closure
Theorems 3.9A and 6.3A, finite poles and affine models for function-field DVRs,
and the valuation-space construction through Proposition 6.7. A separable
two-chart route lets the geometric branch proceed independently of the harder
background normalization theorems. None of these 24 new leaves is yet claimed
formalized.

**Site:** <https://deicyde.github.io/hartshorne/>

[Browse the formalization blueprint](blueprint/README.md).

Built with Lean 4 `v4.33.1` and Mathlib `v4.33.1`.

Developed with [AutoformBot](https://github.com/facebookresearch/autoform-bot).
