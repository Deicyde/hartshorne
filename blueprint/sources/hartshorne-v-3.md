# Hartshorne V.3, monoidal transformations

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter V, §3. The running text occupies printed pp.386–394. Exercises
3.1–3.5 begin on p.394, and Exercises 3.6–3.8 finish at the top of p.395
immediately before §4.

Chapter V's standing convention remains in force: surfaces are nonsingular
projective surfaces over an algebraically closed field.

## Point blowups and exceptional geometry, printed pp.386–387

A monoidal transformation is the blowup `pi:X_tilde -> X` of a surface at a
closed point. It is an isomorphism away from the centre. Proposition 3.1 says
that `X_tilde` is again a nonsingular projective surface, the exceptional
curve `E` is `P^1`, its normal bundle is `O_E(-1)`, and `E^2=-1`.

Remark 3.1.1 announces the converse contraction theorem proved later in V.5.7;
it is not a V.3 proof root.

Proposition 3.2 gives

`Pic(X_tilde) ~= pi^*Pic(X) direct-sum Z*[E]`.

Pullback preserves the old intersection form, every pulled-back class is
orthogonal to `E`, `E^2=-1`, and divisor pushforward is adjoint to pullback.
Proposition 3.3 gives

`K_(X_tilde)=pi^*K_X+E`, and `K_(X_tilde)^2=K_X^2-1`.

Thus canonical self-intersection is not birationally invariant.

## Structure-sheaf cohomology, printed pp.387–388

Proposition 3.4 proves

`pi_*O_(X_tilde)=O_X`, and `R^i pi_*O_(X_tilde)=0` for `i>0`.

Formal functions identifies the completed stalks with the inverse limits of
the cohomology of the infinitesimal exceptional neighbourhoods. Their
successive quotients are `O_E(n)` for `n>0`, whose positive cohomology
vanishes. Normality and birationality identify the degree-zero pushforward;
the acyclic Leray comparison then gives

`H^i(X_tilde,O)=H^i(X,O)`.

Corollary 3.5 and Remark 3.5.1 deduce invariance of arithmetic genus,
geometric genus, and irregularity under a point blowup.

## Strict transforms and multiplicity, printed pp.388–390

For an effective Cartier divisor `C` and a point `P`, its multiplicity is the
largest `r` for which a local equation lies in `m_P^r`. It is positive exactly
when `P` lies on `C`, and equals one exactly when `C` is nonsingular at `P`.

The strict transform is the blowup of `C` at the induced centre, equivalently
the closure away from `E`. Proposition 3.6 proves the total-transform formula

`pi^*C=C_tilde+rE`.

The proof uses the affine blowup chart
`A[t,u]/(t*y-u*x)` and the leading homogeneous form of a local equation.
Corollary 3.7 gives

`C_tilde.E=r`, and
`p_a(C_tilde)=p_a(C)-r*(r-1)/2`.

Proposition 3.8 resolves an irreducible curve on a smooth surface by
successively blowing up its singular points: every nontrivial step strictly
decreases its nonnegative arithmetic genus.

## Embedded resolution, printed pp.390–392

A divisor has normal crossings when every component is nonsingular and the
local equations of all components through a point extend to a regular system
of parameters. The general-resolution history in Remark 3.8.1 is contextual;
the precise theorem proved here is the surface-curve case.

Theorem 3.9 says that every curve on a smooth surface admits a finite sequence
of point blowups whose reduced total inverse image is a normal-crossings
divisor. Resolve each irreducible component first. For the reduced total
transform, blowing up a point of total multiplicity `r` changes arithmetic
genus by

`-(r-1)*(r-2)/2`.

Multiplicity at least three therefore forces a drop. A non-nodal double point
either resolves, produces a triple point after one further blowup, or leaves a
double singularity whose next total multiplicity is three. Termination follows
from nonnegativity of arithmetic genus. Example 3.9.1 records that a cusp needs
one blowup to smooth its strict transform but three for normal crossings of the
total transform.

## Infinitely near points and singularity equivalence, printed pp.392–394

Infinitely near points are points on successive blown-up models, identified
through later maps that are isomorphisms nearby. Example 3.9.2 gives, for an
irreducible curve with normalization `C_bar`,

`g(C_bar)=p_a(C)-sum_P r_P*(r_P-1)/2`,

where the sum includes all infinitely near singular points. Example 3.9.3
localizes this formula to compute the normalization defect `delta_P`.

Remark 3.9.4 defines resolution equivalence of reduced curve singularities by
matching the components, singular points, multiplicities, incidence, and
transition maps in embedded resolutions. Example 3.9.5 classifies double
points by their blowup tree and last node/cusp alternative.

The final comparison with analytic isomorphism uses I Exercise 5.14(d). It is
valid only in characteristic different from two: every plane double point is
analytically isomorphic to `y^2=x^r` for a unique `r>=2`, and blowing up
replaces `r` by `r-2`. The unqualified running sentence must not be promoted
to an arbitrary-characteristic theorem.

## Exercise disposition, printed pp.394–395

- **Exercise 3.1 — OUT.** Arithmetic-genus invariance for blowing up a smooth
  centre in arbitrary dimension is not used by later included running text.
- **Exercise 3.2 — OUT.** It expresses intersections by products of
  multiplicities at ordinary and infinitely near points. V.4.5 says only
  “cf.” after Bézout already supplies the ninth-point argument; the other V.4
  occurrence is an exercise-only hint.
- **Exercise 3.3 — OUT.** Ampleness of `2*pi^*D-E` is not used later.
- **Exercise 3.4 — OUT.** The Hilbert–Samuel polynomial, local multiplicity,
  and cone-vertex calculation have no later running dependency.
- **Exercise 3.5 — OUT.** Its hyperelliptic construction is not used later.
- **Exercises 3.6–3.8 — OUT.** These comparisons and explicit singularity
  calculations elaborate the running classification but are not inputs to a
  later included proof.

Thus no V.3 exercise is adopted.

## Reactivated earlier prerequisite

Running Example 3.9.5 reactivates I Exercise 5.14(d), together with the
completed-local-ring definition of analytic isomorphism from I.5.6. The
result is isolated as a characteristic-not-two, not-ready prerequisite tagged
to `chapter-i-section-5-exercises`. No other earlier exercise is newly
activated.

## External sources, blockers, and context

- The analytic double-point normal form is the one new explicit source
  blocker. Hartshorne states it as a starred exercise; a proof-level formal-
  power-series classification source remains to be adopted.
- Structure-sheaf higher-direct-image vanishing derives the existing formal-
  functions comparison and regular-sequence associated-graded blockers. They
  are inherited infrastructure blockers, not new V.3 roots.
- Hartshorne proves strict-transform resolution and embedded resolution of
  curves on surfaces in the running text. The broader historical resolution
  survey is context, not a package of formal leaves.
- The contraction of a `(-1)`-curve and factorization of birational surface
  maps belong to their later V.5 proofs.

## Pinned Mathlib audit and false friends

The pinned checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). No V.3 leaf is an
exact pinned-Mathlib result.

`RingTheory.ReesAlgebra` defines the Rees algebra and proves finite-generation
facts, but its module documentation explicitly leaves construction of blowups
for future work. Pinned Mathlib has no scheme blowup, exceptional divisor,
strict transform, transform-intersection formula, or resolution theorem.
The homological `Resolution` namespaces are unrelated. Adic-completion,
module-length, and multiplicity APIs are partial algebraic infrastructure and
do not classify analytic plane-curve singularities.

## Representation choices and warnings

- Reuse the project quotient-`Proj` blowup convention. For the exceptional
  divisor, `I_E=O(-E)` and `N_(E/X_tilde)=O_E(-1)`; reversing the Rees grading
  reverses these signs.
- Keep total Cartier pullback, strict transform, and reduced total inverse
  image as three distinct constructions.
- Define point multiplicity by maximal-ideal order before proving the total-
  transform formula; do not identify it prematurely with Hilbert–Samuel
  multiplicity from excluded Exercise 3.4.
- Formal-functions quotients are `I_E^n/I_E^(n+1)=O_E(n)` with this ideal-
  sheaf convention.
- Arithmetic genus in Theorem 3.9 is applied to connected reduced divisors,
  not only integral curves.
- Treat infinitely near points modulo subsequent maps that are local
  isomorphisms, and retain all incidence data in resolution equivalence.
- Restrict the analytic normal-form comparison to `char k != 2`.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Point monoidal transformation | `surfaces/monoidal-transformations/foundations/point-monoidal-transformation.md` |
| Smooth projective point blowup | `surfaces/monoidal-transformations/foundations/point-blowup-smooth-projective-surface.md` |
| Exceptional curve is a projective line | `surfaces/monoidal-transformations/foundations/exceptional-curve-projective-line.md` |
| Exceptional normal bundle | `surfaces/monoidal-transformations/foundations/exceptional-curve-normal-bundle.md` |
| Exceptional self-intersection | `surfaces/monoidal-transformations/foundations/exceptional-curve-self-intersection.md` |
| Proposition 3.2, Picard group | `surfaces/monoidal-transformations/foundations/point-blowup-picard-decomposition.md` |
| Pullback intersection form | `surfaces/monoidal-transformations/foundations/blowup-pullback-intersection-isometry.md` |
| Exceptional orthogonality and projection formula | `surfaces/monoidal-transformations/foundations/exceptional-orthogonality-projection-formula.md` |
| Proposition 3.3, canonical divisor | `surfaces/monoidal-transformations/foundations/point-blowup-canonical-divisor.md` |
| Canonical square drop | `surfaces/monoidal-transformations/foundations/point-blowup-canonical-square.md` |
| Exceptional infinitesimal-neighbourhood filtration | `surfaces/monoidal-transformations/cohomology/exceptional-infinitesimal-neighborhood-filtration.md` |
| Higher direct-image vanishing | `surfaces/monoidal-transformations/cohomology/point-blowup-higher-direct-image-vanishing.md` |
| Structure-sheaf cohomology comparison | `surfaces/monoidal-transformations/cohomology/point-blowup-structure-sheaf-cohomology.md` |
| Corollary 3.5 | `surfaces/monoidal-transformations/cohomology/point-blowup-arithmetic-genus-invariance.md` |
| Geometric genus and irregularity | `surfaces/monoidal-transformations/cohomology/point-blowup-geometric-genus-irregularity.md` |
| Strict transform interface | `surfaces/monoidal-transformations/strict-transforms/strict-transform-api.md` |
| Divisor multiplicity at a point | `surfaces/monoidal-transformations/strict-transforms/divisor-point-multiplicity.md` |
| Local point-blowup charts | `surfaces/monoidal-transformations/strict-transforms/point-blowup-local-charts.md` |
| Proposition 3.6 | `surfaces/monoidal-transformations/strict-transforms/divisor-total-transform-formula.md` |
| Strict-transform intersection with the exceptional curve | `surfaces/monoidal-transformations/strict-transforms/strict-transform-exceptional-intersection.md` |
| Corollary 3.7, genus drop | `surfaces/monoidal-transformations/strict-transforms/strict-transform-arithmetic-genus-drop.md` |
| Proposition 3.8 | `surfaces/monoidal-transformations/strict-transforms/irreducible-curve-resolution.md` |
| Normal crossings and reduced total transform | `surfaces/monoidal-transformations/resolution/normal-crossings-reduced-total-transform.md` |
| Reduced-total-transform genus drop | `surfaces/monoidal-transformations/resolution/reduced-total-transform-genus-drop.md` |
| Resolve irreducible components first | `surfaces/monoidal-transformations/resolution/resolve-components-first.md` |
| Double-point blowup alternatives | `surfaces/monoidal-transformations/resolution/double-point-post-blowup-trichotomy.md` |
| Theorem 3.9 | `surfaces/monoidal-transformations/resolution/embedded-resolution-curves-surfaces.md` |
| Example 3.9.1 | `surfaces/monoidal-transformations/resolution/cusp-embedded-resolution-example.md` |
| Infinitely near points | `surfaces/monoidal-transformations/resolution/infinitely-near-points.md` |
| Examples 3.9.2–3 | `surfaces/monoidal-transformations/resolution/normalization-genus-delta-multiplicity-sums.md` |
| Resolution equivalence and double-point tree | `surfaces/monoidal-transformations/resolution/resolution-equivalence-double-point-tree.md` |
| Analytic normal-form comparison | `surfaces/monoidal-transformations/resolution/double-point-analytic-normal-form-comparison.md` |

## Reactivated-prerequisite map

| Source result | Roadmap article |
|---|---|
| I Exercise 5.14(d) and analytic-isomorphism definition | `surfaces/prerequisites/plane-double-point-analytic-normal-form.md` |
