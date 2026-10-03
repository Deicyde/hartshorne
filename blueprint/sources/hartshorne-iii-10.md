# Hartshorne III.10, smooth morphisms

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter III, §10. The running text occupies printed pp.268–275. The exercises
begin on p.275 and continue through p.276. This roadmap adopts every running
result and only Exercise 10.3, whose definition of unramified morphisms is used
later in Chapter IV.

All schemes in the section are of finite type over a fixed field `k`.
Formalization should use Mathlib schemes over `Spec k`. A Hartshorne variety is
represented by an integral separated finite-type scheme over `k`; this avoids
reintroducing the project's older classical `Variety` as the implementation
type for smoothness.

## Smoothness and geometric fibres, pp.268–270

Hartshorne defines `f : X -> Y` to be smooth of relative dimension `n` by
three simultaneous conditions: `f` is flat; corresponding irreducible
components have dimension difference `n`; and every fibre of `Omega[X/Y]` has
dimension `n`. Examples 10.0.1–3 give affine and projective space, the
locally-free differential criterion for integral `X`, and the equivalence
between smoothness over an algebraically closed field and regularity.

Mathlib instead defines `SmoothOfRelativeDimension n` by locally standard
smooth affine charts. The roadmap adopts that implementation notion and
requires an explicit equivalence with Hartshorne's three clauses. It does not
silently treat the two definitions as definitional equalities.

Proposition 10.1 proves smoothness of open immersions and stability under base
change, composition, and products, with the stated relative dimensions.
Theorem 10.2 characterizes a smooth morphism as a flat morphism whose
geometric fibres are regular and equidimensional of dimension `n`. Here
"geometric" means base change to an algebraic closure of the residue field.
Regularity, geometric regularity, reducedness, and smoothness remain distinct
predicates.

Stacks Project §29.35, tag `01V4`, supplies the modern definition and local
calculus. Lemma 29.35.3, tag `01V8`, supplies flat plus smooth fibres implies
smooth. Section 37.21, tag `07R6`, records regular morphisms. Section 10.140,
tag `00TQ`, treats smooth algebras over fields.

## Tangent criterion, pp.270–271

For `x : X`, `y=f(x)`, the tangent map is

`T_x X -> T_y Y tensor_[k(y)] k(x)`.

It is the dual of the natural cotangent map after extending residue-field
scalars; it must not be written as a map of vector spaces over the wrong
field. Lemma 10.3A is the local criterion of flatness across a non-zero-divisor.
Hartshorne cites Bourbaki, *Algèbre commutative*, III §5, and
Altman–Kleiman, *Introduction to Grothendieck Duality Theory*, V §3. These
references are adopted for that lemma.

Proposition 10.4 says that for a morphism of nonsingular varieties over an
algebraically closed field, with `dim X = dim Y + n`, the following are
equivalent: smoothness of relative dimension `n`; local freeness of
`Omega[X/Y]` of rank `n`; and surjectivity of every closed-point tangent map.
This proposition depends on the II.8 regular-local and differential criteria;
it does not redefine nonsingularity.

## Characteristic-zero generic smoothness, pp.271–272

Lemma 10.5 says that a dominant morphism of integral finite-type schemes over
an algebraically closed field of characteristic zero is smooth on a nonempty
open subset of the source. Its field-theoretic input is that
`K(X)/K(Y)` is separably generated. Characteristic zero begins here and is
retained in Proposition 10.6, Corollary 10.7, and Theorem 10.8.

Example 10.5.1 is the required positive-characteristic warning: Frobenius on
`P^1` has relative dimension zero but is nowhere smooth because its differential
vanishes and `Omega[X/Y]` has rank one. Exercise 10.1 gives a separate warning
over an imperfect field—regular need not imply smooth—but that exercise is
outside the adopted fine scope.

For the closed-point locus

`X_r = {x | rank(Tf_x) <= r}`,

Proposition 10.6 proves `dim closure(f(X_r)) <= r`; the closure makes explicit
Hartshorne's convention for the dimension of an arbitrary image. The roadmap
first constructs a finite locally closed rank stratification from coherent
cotangent presentations and local matrix minors, then passes to dense smooth
irreducible strata; the closed-point subset is not treated as though it
already carried a global determinantal scheme structure. Corollary
10.7 then gives a nonempty open `V` in `Y` over which a morphism from a
nonsingular source is smooth. If `f` is not dominant, the restricted source
may be empty. Stacks Lemma 33.25.7, tag `056V`, is related prior art for dense
smooth loci over fields, but is not this relative generic-smoothness theorem.

## Homogeneous spaces, Kleiman, and Bertini, pp.272–275

The implementation uses genuine algebraic data. A group variety is an
integral separated finite-type group object in `Over (Spec k)`. An action is a
morphism `G times_k X -> X` over `k` satisfying the unit and associativity
diagrams. A homogeneous space requires transitivity on `k`-points; over
algebraically closed `k`, these are the closed points. Translates are induced
by `k`-point sections of the group object, not by an unrelated abstract group
action.

The proof that a homogeneous space is regular transports one nonempty regular
open by translate automorphisms. The translates cover all closed points, and
the complement is empty because a finite-type scheme over a field is Jacobson.
This orbit-openness argument must be formalized rather than assuming
transitivity on all scheme points.

For Bertini, `PGL(n+1)` must be constructed as a genuine finite-type group
scheme with its algebraic action on `P^n`; Mathlib's abstract group
`Matrix.ProjGenLinGroup` alone is insufficient. This construction is a
project-specified source obligation and leaves the Bertini application not
ready until its scheme-level representation is adopted. The roadmap also
separates projective-space homogeneity from the smooth, open orbit morphism
`PGL(n+1) -> (P^n)^dual`; the latter is what turns a group-open family of good
translates into an open family of good hyperplanes.

Theorem 10.8 is Kleiman's general-translate theorem. For a homogeneous `X`
and nonsingular `Y,Z -> X`, a general translate has fibre product either empty
or nonsingular of exactly

`dim Y + dim Z - dim X`.

The incidence scheme is nonsingular and equidimensional because its map to
`Z` is a smooth base change of the action-family morphism. Its regular fibres
are locally connected and quasi-compact, hence have finitely many connected
components; equidimensionality and the constant relative dimension of the
smooth incidence projection give every nonempty component the expected
dimension. This is the precise interpretation of Hartshorne's component
remark; regularity alone is not used to infer equidimensionality. Since the incidence
scheme need not be irreducible, the roadmap includes a finite-component
generic-smoothness wrapper rather than applying Corollary 10.7 outside its
variety hypothesis.

The adopted external source is Kleiman, “The transversality of a general
translate,” *Compositio Mathematica* 28 (1974), 287–297. Corollary 10.9 derives
the characteristic-zero basepoint-free Bertini theorem. It is a distinct
statement and proof route from Hartshorne II.8.18: the III.10 node must
cross-link, not conflate, the earlier embedded-hyperplane theorem. Stacks
§33.47, tag `0FD4`, is adopted supplementary Bertini prior art.

Remark 10.9.1's connectedness assertion belongs to III Exercise 11.3 and is
deferred. Remark 10.9.2's finite-dimensional and base-locus variants are
corollaries of the Bertini leaf. Remark 10.9.3 points back to Frobenius in
positive characteristic. Remark 10.9.4 is the comparison with II.8.18.

## Exercise disposition, pp.275–276

Exercise 10.3 is adopted. It defines unramified morphisms by
`m_y O_x = m_x` together with separability of `k(x)/k(y)`, and proves

`etale <-> flat and Omega[X/Y]=0 <-> flat and unramified`.

This is used at IV.2, printed p.299, to compare ramification indices with the
scheme-theoretic definition, and at IV Exercise 4.8, printed p.338, in the
definition of the algebraic fundamental group. Stacks §29.37, tag `02GH`, and
Lemma 29.37.15, tag `02GU`, are adopted supplementary references.

Exercises 10.1–10.2 and 10.4–10.9 are **OUT**. Their topics are respectively:
regular but nonsmooth schemes over imperfect fields; spreading smoothness from
a proper flat fibre; completed-local-ring criteria for étaleness; étale-local
descent of local freeness; a disconnected finite étale cover of a nodal cubic;
two moving-singularity examples; and miracle flatness. No later running-text
dependency was found except the two uses of Exercise 10.3 above. Exercise 10.4
would additionally inherit the unresolved compatible coefficient-field issue
from II.8.25A.

## Pinned Mathlib audit

The audited checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). Stable exact prior
art includes:

- `AlgebraicGeometry.Smooth`, `SmoothOfRelativeDimension`,
  `smoothOfRelativeDimension_isStableUnderBaseChange`,
  `smoothOfRelativeDimension_comp`, `Scheme.Hom.smoothLocus`, and
  `Scheme.Hom.isOpen_smoothLocus` in
  `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`;
- `Smooth.of_smooth_fiberToSpecResidueField` in
  `Mathlib/AlgebraicGeometry/Morphisms/SmoothFiber.lean`;
- `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` and
  `Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth` in
  `Mathlib/RingTheory/Smooth/StandardSmoothCotangent.lean`;
- `Etale.iff_smoothOfRelativeDimension_zero` and
  `Etale.iff_flat_and_formallyUnramified` in
  `Mathlib/AlgebraicGeometry/Morphisms/Etale.lean`;
- `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq` in
  `Mathlib/RingTheory/Unramified/LocalRing.lean`;
- `AlgebraicGeometry.smooth_of_grpObj` in
  `Mathlib/AlgebraicGeometry/Group/Smooth.lean`.

These are proof infrastructure, not exact whole declarations for any
source-shaped leaf below. In particular, no leaf should be marked
`mathlib: true`. No pinned result was found for Hartshorne's three-clause
criterion, geometric regularity of scheme fibres, the scheme tangent map,
Lemma 10.3A, relative generic smoothness, the rank-image dimension estimate,
homogeneous-space actions, Kleiman transversality, or the PGL Bertini
application.
