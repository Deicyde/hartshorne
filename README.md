# Hartshorne, Algebraic Geometry

A Lean 4 formalization of the classical variety theory in Chapter I of Robin
Hartshorne, *Algebraic Geometry* (Springer, Graduate Texts in Mathematics 52,
1977), built on Mathlib.

Sections I.1 through I.4, the geometric core of I.5 through Theorem I.5.3, and
I.6 through Corollary I.6.12 are decomposed into a dependency graph of 163
formalization targets. The completion, Cohen-structure, and analytic-isomorphism
material later in §I.5 is deferred. Chapter V §§5–6 and
Appendices A–C have an approved coarse whole-book map. Section I.7 is decomposed into 50 fine targets,
47 formalized and three remaining; the §I.8 survey has been dispositioned claim
by claim; and all of Chapter II now has a 444-leaf fine roadmap, including 99
exact pinned-Mathlib results. The later milestones remain deferred. See the
[coverage contract](blueprint/coverage/README.md) for exactly what is and is not
claimed.

All of Chapter III has a 288-leaf cohomology roadmap: nineteen exact pinned-Mathlib
results and 269 project targets. It covers derived functors,
sheaf and supported cohomology, affine vanishing, local cohomology, and Čech
comparison, projective cohomology, Ext, dualizing sheaves, and Serre duality
through higher direct images, flat families, Hilbert polynomials, deformations,
smooth morphisms, generic smoothness, Bertini, formal functions, Stein
factorization, semicontinuity, Grauert's theorem, and base change through p. 292.

All of Chapter IV has a 201-leaf curve roadmap: two exact pinned-Mathlib
results and 199 project targets for Riemann–Roch, ramification, projective
embeddings, elliptic and canonical curves, Clifford's theorem, moduli,
Castelnuovo's bound, and space-curve classifications. Five additional project
leaves reactivate Exercises I.3.14(a), I.5.4, I.5.6(b), I.7.3, and II.6.4.

Chapter V §§1–4 has a 165-leaf surface roadmap: one exact pinned-Mathlib result
and 164 project targets for intersection theory, ruled surfaces, point
blowups, embedded resolution, cubic surfaces, and the 27 lines. Four additional project leaves
reactivate III Exercise 7.4(a),(c),(d), II Exercise 8.2, and I Exercise 5.14(d);
one forward Appendix A
prerequisite records the HRR source of Noether's formula.

**All 163 targets through Corollary I.6.12 are complete.** Of these, 159 are
proved in this project and four are supplied by Mathlib. The active §I.7
milestone has 50 targets, of which 47 are formalized. The first 114 completed targets run
through Lemma I.6.4. Of the
first 86 targets in §§I.1–I.4, 85 are proved here,
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

The completed 26-leaf normalization milestone covers the exact nonseparable integral-closure
Theorems 3.9A and 6.3A, finite poles and affine models for function-field DVRs,
and the valuation-space construction through Proposition 6.7. A separable
two-chart route lets the geometric branch proceed independently of the harder
background normalization theorems. All 26 leaves are formalized, including the
nonseparable normalization theorems, the full valuation-space regular-function
structure, and the isomorphism of a nonsingular curve with its open image in
the valuation space.

The 23-leaf projective-model milestone adopts the local-ring criteria in
Exercise I.3.3 used by Theorem I.6.9, proves Proposition I.6.8, constructs the
nonsingular projective model of Theorem I.6.9, and decomposes Corollaries
I.6.10–6.12 through the contravariant equivalence with one-dimensional
function fields. All 23 leaves are formalized.

The 50-leaf §I.7 milestone develops affine and projective intersection
dimension, integer-graded Hilbert polynomials, projective degree, and Bézout's
theorem. Forty-seven leaves are formalized; the pure-curve degree and two
reducible-curve leaves remain. It includes only the earlier exercises required
by the running proofs; the optional generic-line exercise chain remains out of
scope.

The 444-leaf Chapter II milestone covers sheaves, spectra, schemes,
projective spectra, the classical-variety comparison, first properties,
subschemes, dimension, fibre products, separatedness, properness, projective
morphisms, modules, divisors and Picard groups, linear systems, relative Proj,
projective bundles, blowups, differentials, canonical sheaves, and lci geometry.
Ninety-nine leaves are exact pinned-Mathlib results; the other 345 are planned
project wrappers, representation bridges, or missing theorems.

**Site:** <https://deicyde.github.io/hartshorne/>

[Browse the formalization blueprint](blueprint/README.md).

Built with Lean 4 `v4.33.1` and Mathlib `v4.33.1`.

Developed with [AutoformBot](https://github.com/facebookresearch/autoform-bot).
