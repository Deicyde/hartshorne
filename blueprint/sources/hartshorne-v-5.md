# Hartshorne V.5, birational transformations of surfaces

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter V, §5. The running text occupies printed pp.409–419. Exercises
5.1–5.7 begin on p.419, and Exercise 5.8 and its historical notes finish on
p.420 immediately before §6.

The section proves factorization of birational transformations of nonsingular
projective surfaces, Castelnuovo contraction of a `(-1)`-curve, and existence
of relatively minimal models.

## Birational maps and fundamental points, printed pp.409–411

A birational transformation is represented by a morphism on a dense open
subset and has a largest domain of definition; its complement consists of
fundamental points. The graph is the closure of the graph on that domain.
Hartshorne's total transform of a subset is the image under the second graph
projection of its inverse image under the first; it is set-theoretic and must
not be conflated with scheme-theoretic inverse image.

Lemma 5.1 says that a rational map from a normal projective variety to a
projective variety is defined at every codimension-one point, by the DVR
valuative criterion. Thus the fundamental locus has codimension at least two
and, on a surface, is finite.

Theorem 5.2 is Hartshorne's connected-fibre form of Zariski's Main Theorem:
at a fundamental point, the total transform is connected and positive-
dimensional. Connectedness comes from the projective birational graph
projection. A zero-dimensional fibre would be finite nearby, hence finite and
birational onto a normal target, forcing an isomorphism and contradicting
fundamentality.

## Factorization, printed pp.411–413

Proposition 5.3 says that a birational morphism of smooth projective surfaces
factors through the point blowup of every fundamental point of its inverse.
The proof uses local coordinates on the point blowup and the positive-
dimensional connected inverse image to exclude a new fundamental point over
the exceptional curve.

For a birational morphism `f`, let `n(f)` be the number of irreducible curves
contracted to points. Corollary 5.4 proves finiteness and factors `f` into
exactly `n(f)` point blowups; every factor lowers the count by one and the
zero-count remainder is an isomorphism.

Theorem 5.5 factors an arbitrary birational transformation into point blowups
and their inverses. A smooth curve in a doubled very ample system on the
target defines a nonnegative arithmetic-genus defect. Blowing up a singular
image point lowers the defect; once it reaches zero, Zariski's Main Theorem
rules out any remaining fundamental point. The two birational morphisms to a
common smooth surface then factor by Corollary 5.4.

Corollary 5.6 makes the arithmetic genus of a smooth projective surface a
birational invariant. The higher-dimensional Hironaka and Kodaira–Spencer
remarks and the Sally–Shannon failure of smooth-centre factorization are
contextual comparisons, not additional V.5 leaves.

## Castelnuovo contraction, printed pp.414–416

An exceptional curve of the first kind is a curve `Y~=P^1` with `Y^2=-1`.
Theorem 5.7 says that every such curve is the exceptional curve of the blowup
of a point on another nonsingular projective surface.

Choose a very ample `H` with `H^1(O_X(H))=0`, put `k=H.Y`, and use
`A=O_X(H+kY)`. Exact sequences along `Y` give the necessary `H^1` ladder;
`A` is globally generated, contracts `Y`, and separates points and tangents
away from it. Normalize the projective image.

Formal functions and the exceptional infinitesimal-neighbourhood filtration
identify the completed local ring at the image point with `k[[x,y]]`. The
regularity-reflection clause of I Theorem 5.4A is then needed to deduce that
the uncompleted local ring is regular. Birational-morphism factorization shows
that the map is one point blowup. A final first-order lifting argument shows
that the original image was already normal, so normalization was unnecessary.

Example 5.7.1 constructs elementary transformations of ruled surfaces by
blowing up a point on a fibre and contracting its strict transform.

## General contraction, printed pp.417–418

Remark 5.7.2 defines contractibility and records:

- contraction to a nonsingular point is equivalent to `Y~=P^1`, `Y^2=-1`;
- algebraic contractibility to a possibly singular point forces `Y^2<0`;
- a rational curve with `Y^2<0` contracts projectively;
- over `C`, Grauert analytically contracts every negative curve.

The Grauert theorem is an external analytic source blocker. Example 5.7.3
constructs, over an uncountable algebraically closed field, a negative elliptic
curve that is analytically contractible over `C` but is not algebraically
contractible. The proof uses ten group-law independent points on a plane cubic
and Bézout.

## Relative minimal models, printed pp.418–419

A surface is relatively minimal when every birational morphism from it to
another nonsingular projective surface is an isomorphism. It is a minimal
model when it is the unique relatively minimal model in its birational class.
A surface is relatively minimal exactly when it has no exceptional curve of
the first kind.

Theorem 5.8 proves existence: repeatedly contract `(-1)`-curves. Their total
transforms on the original surface have square minus one and are mutually
orthogonal. Exercise V.1.8(a) makes their classes linearly independent in the
finite-dimensional vector space `H^1(X,Omega_X)`, bounding the length of every
contraction sequence.

Remark 5.8.1 reuses Exercise V.4.15 to note that the starting surface may
nevertheless have infinitely many exceptional curves. The source-supported
construction is over an uncountable algebraically closed field.

The projective plane and rational ruled `X_e`, `e!=1`, are relatively minimal;
`X_1` is not. Every ruled surface over a positive-genus curve is relatively
minimal. Hartshorne quotes the external classification that outside the
rational and ruled cases every surface has a unique minimal model, and that
the displayed rational and ruled examples exhaust their relatively minimal
models.

## Exercise disposition, printed pp.419–420

- **Exercise 5.1 — OUT.** Resolution of a rational function is used only by
  excluded Exercise 5.6.
- **Exercise 5.2 — ADOPTED.** A rational curve with negative square contracts
  to a point on a possibly singular projective surface; running Remark 5.7.2
  states this result.
- **Exercises 5.3–5.6 — OUT.** They give an alternate cohomological
  termination proof, negativity of contraction matrices, elementary-
  transformation classification, and a valuation application, but no later
  included running proof depends on them. Example 5.7.1's “see” reference to
  Exercise 5.5 is optional.
- **Exercise 5.7 — ADOPTED.** If an irreducible curve is the full fibre over a
  contraction point, then it has negative self-intersection; running Remark
  5.7.2 uses this necessity.
- **Exercise 5.8 — OUT.** The `E8` surface singularity and its extensive
  analytic and topological notes have no later included running dependency.

Thus exactly Exercises 5.2 and 5.7 are adopted.

## Reactivated and reused prerequisites

Step 5 of Castelnuovo contraction reactivates exactly the regularity-under-
completion clause of I Theorem 5.4A. It is isolated in the new source unit
`chapter-i-theorem-5-4a`; all other completion, Cohen-structure, and analytic
material in the old I.5 completion block remains deferred.

Remark 5.8.1 reuses the already-adopted V Exercise 4.15(b,c,e) construction;
it does not create another exercise leaf.

## External sources and blockers

- Grauert's analytic contraction of an arbitrary negative curve over `C` is
  an explicit V.5 source blocker.
- Zariski [5], [6], [9] is required for uniqueness of minimal models outside
  the rational and ruled classes.
- Nagata [5] or Hartshorne [4] is required for classification of relatively
  minimal rational and ruled surfaces.
- Castelnuovo contraction derives the new not-ready I.5.4A completion-
  regularity prerequisite and the existing formal-functions / associated-
  graded blockers; these are inherited infrastructure obligations.

Thus V.5 has three explicit section blockers and one newly reactivated
earlier blocker.

## Pinned Mathlib audit and false friends

The pinned checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). No V.5 leaf is an
exact pinned-Mathlib result.

The recent `AlgebraicGeometry.ZariskisMainTheorem` proves the modern
quasi-finite-locus/relative-normalization formulation and the consequence that
proper locally quasi-finite morphisms are finite. It does not supply
Hartshorne's connected positive-dimensional total transform of a fundamental
point. The birational `PartialMap`/`RationalMap`, properness, normalization,
formal completion, and finite-morphism APIs are useful infrastructure only.

Pinned Mathlib contains no factorization of birational surface maps,
Castelnuovo contraction, elementary transformation, relatively minimal model,
or uniqueness/classification theorem.

## Representation choices and warnings

- Represent a birational transformation by its maximal-domain rational map,
  and keep its graph and set-theoretic total transform separate from a scheme
  fibre or pullback.
- Track the finite set of irreducible contracted curves, not merely
  fundamental points; Corollary 5.4 counts factors by curves.
- Preserve the normalization and completed-local-ring stages in
  Castelnuovo's construction. Completion regularity does not follow from the
  currently pinned API.
- Distinguish algebraic contraction to a projective scheme from Grauert's
  analytic contraction.
- Keep “relatively minimal” distinct from “the unique minimal model.”
- Retain uncountability in the Hironaka and infinite-exceptional-curve
  examples where the source uses countable-avoidance arguments.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Maximal domain and fundamental points | `surfaces/birational-transformations/fundamental-loci/birational-transformation-maximal-domain.md` |
| Graph and total transform | `surfaces/birational-transformations/fundamental-loci/birational-graph-total-transform.md` |
| Lemma 5.1 | `surfaces/birational-transformations/fundamental-loci/normal-source-fundamental-locus-codimension-two.md` |
| Inverse of a point blowup | `surfaces/birational-transformations/fundamental-loci/point-blowup-inverse-fundamental-point.md` |
| Theorem 5.2, connectedness | `surfaces/birational-transformations/fundamental-loci/fundamental-point-total-transform-connected.md` |
| Finite-fibre neighbourhood step | `surfaces/birational-transformations/fundamental-loci/finite-fibre-neighborhood-quasifinite.md` |
| Theorem 5.2, positive dimension | `surfaces/birational-transformations/fundamental-loci/fundamental-point-total-transform-positive-dimensional.md` |
| Proposition 5.3 | `surfaces/birational-transformations/factorization/fundamental-point-factor-through-blowup.md` |
| Finiteness of contracted curves | `surfaces/birational-transformations/factorization/contracted-curves-finite.md` |
| One factor lowers the count | `surfaces/birational-transformations/factorization/blowup-factor-reduces-contracted-curve-count.md` |
| Corollary 5.4 | `surfaces/birational-transformations/factorization/birational-morphism-point-blowup-factorization.md` |
| Genus-defect descent | `surfaces/birational-transformations/factorization/hyperplane-curve-genus-defect-decreases.md` |
| Theorem 5.5 | `surfaces/birational-transformations/factorization/birational-surface-map-common-resolution-factorization.md` |
| Corollary 5.6 | `surfaces/birational-transformations/factorization/surface-arithmetic-genus-birational-invariant.md` |
| Exceptional curve of the first kind | `surfaces/birational-transformations/contraction/exceptional-curve-first-kind.md` |
| Castelnuovo cohomology ladder | `surfaces/birational-transformations/contraction/castelnuovo-h1-ladder.md` |
| Global generation of the contraction sheaf | `surfaces/birational-transformations/contraction/castelnuovo-contraction-global-generation.md` |
| Contraction morphism | `surfaces/birational-transformations/contraction/castelnuovo-contraction-morphism.md` |
| Normalized projective image | `surfaces/birational-transformations/contraction/castelnuovo-normalized-image.md` |
| Exceptional infinitesimal neighbourhoods | `surfaces/birational-transformations/contraction/exceptional-curve-infinitesimal-neighborhoods.md` |
| Completed-local-ring regularity | `surfaces/birational-transformations/contraction/castelnuovo-completed-local-regularity.md` |
| Theorem 5.7 | `surfaces/birational-transformations/contraction/castelnuovo-contraction.md` |
| Original image already normal | `surfaces/birational-transformations/contraction/castelnuovo-image-already-normal.md` |
| Elementary transformation | `surfaces/birational-transformations/contraction/ruled-surface-elementary-transform.md` |
| Contractibility interface | `surfaces/birational-transformations/contraction/contractible-curve-definition.md` |
| Necessity of negative square | `surfaces/birational-transformations/contraction/contracted-curve-negative-square.md` |
| Sufficiency for a negative rational curve | `surfaces/birational-transformations/contraction/negative-rational-curve-projective-contraction.md` |
| Grauert analytic contraction | `surfaces/birational-transformations/contraction/grauert-analytic-negative-curve-contraction.md` |
| Hironaka nonalgebraic example | `surfaces/birational-transformations/contraction/hironaka-negative-elliptic-nonalgebraic-contraction.md` |
| Relative-minimal definitions and criterion | `surfaces/birational-transformations/minimal-models/relative-minimal-surface-criterion.md` |
| Orthogonality and contraction bound | `surfaces/birational-transformations/minimal-models/contraction-orthogonality-cohomology-bound.md` |
| Theorem 5.8 | `surfaces/birational-transformations/minimal-models/relative-minimal-model-existence.md` |
| Remark 5.8.1 | `surfaces/birational-transformations/minimal-models/infinite-exceptional-curves-compatible-minimality.md` |
| Example 5.8.2 | `surfaces/birational-transformations/minimal-models/rational-relative-minimal-examples.md` |
| Example 5.8.3 | `surfaces/birational-transformations/minimal-models/positive-genus-ruled-relative-minimal.md` |
| Nonruled minimal-model uniqueness | `surfaces/birational-transformations/minimal-models/nonruled-minimal-model-uniqueness.md` |
| Rational/ruled relatively minimal classification | `surfaces/birational-transformations/minimal-models/rational-ruled-relative-minimal-classification.md` |
| Exercise 5.2 | `surfaces/birational-transformations/exercises/negative-rational-curve-contraction.md` |
| Exercise 5.7 | `surfaces/birational-transformations/exercises/contracted-curve-negative-self-intersection.md` |

## Reactivated and reused prerequisite map

| Source result | Roadmap article |
|---|---|
| I Theorem 5.4A, regularity under completion | `surfaces/prerequisites/regular-local-iff-completion-regular.md` |
| V Exercise 4.15(b,c,e), infinite exceptional curves | `surfaces/cubic-surfaces/exercises/infinitely-many-exceptional-curves-general-blowups.md` |
