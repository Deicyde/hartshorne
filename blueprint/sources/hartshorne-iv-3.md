# Hartshorne IV.3, embeddings in projective space

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter IV, §3, printed pp.307–316. The running text occupies pp.307–315 and
the twelve exercises continue through p.316. The roadmap adopts every
mathematical claim in the running text and only Exercises 3.4(b)–(d),
3.6(a)–(b), and 3.9, which are used by later running text.

Chapter IV's standing convention remains in force: a curve is an integral,
proper, regular one-dimensional scheme over a fixed algebraically closed
field `k`, hence projective. A point means a closed point. Projective
embeddings and their degrees are scheme-theoretic; Mathlib's quotient type of
abstract projective points is not used as a substitute.

## Linear systems and embeddings, printed pp.307–309

Proposition 3.1 translates the separation criteria from II.7 into divisor
language. For a divisor `D` on a curve:

- `|D|` is basepoint free exactly when
  `dim|D-P| = dim|D|-1` for every point `P`;
- `D` is very ample exactly when
  `dim|D-P-Q| = dim|D|-2` for every pair `P,Q`, including `P=Q`.

The repeated-point case is the tangent-vector condition. Corollary 3.2 uses
Riemann–Roch: degree at least `2g` implies basepoint freeness, and degree at
least `2g+1` implies very ampleness. Corollary 3.3 says a divisor on a curve
is ample exactly when it has positive degree.

For an embedding defined by a very ample divisor `D`, the projective degree
of the image is `deg D`. On a genus-zero curve, positive degree, ampleness,
and very ampleness agree. Every degree-three divisor on an elliptic curve is
very ample and embeds it as a plane cubic; conversely a divisor of degree two
cannot embed it. Every genus-two curve has a degree-five embedding in
`P^3`. The plane-quartic example records that the uniform `2g+1` bound need
not be sharp.

## Projection and embeddings in projective three-space, pp.309–310

Projection from a point is the morphism of I Exercise 3.14(a). For an embedded
curve, define secant lines through distinct pairs and tangent lines using the
embedded tangent space.

Proposition 3.4 says projection from `O` is a closed immersion exactly when
`O` lies on no secant and no tangent. Proposition 3.5 constructs the secant
incidence family, of dimension at most three, and the tangent incidence
family, of dimension at most two. When the ambient dimension is at least
four their union is proper, so a center outside it gives a closed immersion
into one lower-dimensional projective space. Repeating this proves Corollary
3.6: every curve embeds in `P^3`.

The implementation must construct incidence schemes and their evaluation
morphisms. A bare set-theoretic union of lines does not expose the dimension
argument or the fibre over a proposed projection center.

## Nodal projections and bad secants, pp.310–314

For `X subset P^3`, Proposition 3.7 characterizes when projection from `O`
is birational with only nodes in the image:

1. only finitely many secants pass through `O`;
2. no tangent passes through `O`;
3. no multisecant passes through `O`;
4. no secant through `O` joins points with coplanar tangent lines.

The node here is the ordinary double point of I Exercise 5.6(b). Conditions
2–4 ensure that each identified pair gives two transverse branches, while
condition 1 gives generic injectivity.

Proposition 3.8 proves that if every secant is a multisecant, then every pair
of tangent lines is coplanar; if every pair of tangent lines is coplanar, one
point lies on every tangent. A curve with such a point is *strange*. A line is
strange, and a conic in characteristic two is strange.

Theorem 3.9, attributed to Samuel, says these are the only strange curves.
After projection from the common tangent point, vanishing differential forces
the projected coordinate functions to be `p`th powers. A second projection
to `P^1`, together with Riemann–Hurwitz and a hyperplane-intersection count,
forces either degree one, or degree two in characteristic two.

Theorem 3.10 constructs a good projection center. Proposition 3.8 and
Theorem 3.9 show that the multisecant and coplanar-tangent pairs form proper
subsets. Their secant unions and the tangent variety have dimension at most
two. For the remaining finite-secant condition, apply the later-used
II Exercise 3.7 to the secant-incidence morphism over a dense open of `P^3`.
Corollary 3.11 gives every curve a birational plane model with only nodes.

## Severi loci, printed pp.314–315

Remark 3.11.1 considers the locus `V_(d,r)` of irreducible degree-`d` plane
curves with `r` nodes. It is locally closed in the projective parameter space
of degree-`d` equations. Normalization and the delta-one node calculation give

`g = (d-1)(d-2)/2 - r`,

so nonemptiness requires `0 <= r <= (d-1)(d-2)/2`. Both extremes occur:
Bertini gives the nonsingular case and nodal projection of the rational normal
curve gives the rational case.

Hartshorne then states the Severi theorem: every allowed `V_(d,r)` is nonempty
and irreducible of dimension `d(d+3)/2-r`. This is not proved in the text.
The theorem leaf remains `not_ready` until a precise passage in Joe Harris,
“On the Severi problem,” *Inventiones Mathematicae* 84 (1986), 445–461,
or another proof-level source is adopted.

## Exercise disposition, printed pp.315–316

- **Exercises 3.1–3.3 — OUT.** Later appearances are exercise-only or
  parenthetical comparisons; the running canonical-curve text proves the
  needed plane-quartic facts independently.
- **Exercise 3.4(a) — OUT.** Projective normality and generators of the ideal
  of the rational normal curve have no later running-text dependency here.
- **Exercise 3.4(b)–(d) — ADOPTED.** The minimal-degree classification and
  its conic/cubic consequences are used in the running low-degree
  classification in IV.6 and in the canonical-image discussion in IV.5.
- **Exercise 3.5 — OUT.** Its projection degeneration is not used by later
  included running text.
- **Exercise 3.6(a)–(b) — ADOPTED.** The degree-four trichotomy and the
  two-quadric description of elliptic quartics are cited in the running
  classification in IV.6.
- **Exercises 3.7–3.8 — OUT.** Their lifting counterexample and singular
  strange-curve examples have no later included running-text dependency.
- **Exercise 3.9 — ADOPTED.** A general plane cuts a nonplanar degree-`d`
  curve in `d` distinct points with no three collinear; the running proof of
  Castelnuovo's Theorem IV.6.4 uses this result.
- **Exercises 3.10–3.12 — OUT.** The characteristic-zero multisecant theorem,
  higher-dimensional projection/Veronese exception, and low-degree nodal
  existence list have no later included running-text dependency.

Two earlier exercises are newly activated by the running proof: I Exercise
3.14(a), projection from a point, and the ordinary-node definition/criterion
in I Exercise 5.6(b). II Exercise 3.7 was already adopted and is represented
by the existing generically-finite-to-finite-open article.

## External sources and blockers

- Samuel's classification is cited as P. Samuel, *Lectures on Old and New
  Results on Algebraic Curves*, Tata Institute of Fundamental Research
  (1966). Hartshorne supplies a proof, so this citation is supplementary.
- The Severi theorem requires the Harris source above. It is the only new
  source-blocked node in this section.
- The incidence-scheme, projection, and strange-curve APIs are substantial
  implementation projects, but their mathematical statements and proofs are
  fixed by Hartshorne and are not marked source-blocked.

## Pinned Mathlib audit and false friends

The audited checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). It contains scheme
projective spectra, closed immersions, fibre products, and the underlying
linear algebra of projective spaces. It has no exact result for projection
from a center, secant or tangent incidence schemes, embeddings of curves in
`P^3`, strange curves, nodal plane models, rational normal curve
classification, or Severi varieties. No IV.3 leaf is an exact Mathlib leaf.

`LinearAlgebra.Projectivization`, including its recent collinearity and group
action API, is pointwise linear algebra. It is not projective space as a
scheme and supplies neither regular projection morphisms nor scheme images
and dimension bounds. The projective formulas in
`AlgebraicGeometry.EllipticCurve` likewise concern explicit Weierstrass-point
models, not arbitrary Chapter-IV curves or their complete linear systems.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Proposition 3.1 | `curves/projective-embeddings/linear-series/curve-linear-system-dimension-criteria.md` |
| Corollary 3.2 | `curves/projective-embeddings/linear-series/high-degree-basepoint-free-very-ample.md` |
| Corollary 3.3 | `curves/projective-embeddings/linear-series/curve-ample-iff-positive-degree.md` |
| Example 3.3.2 | `curves/projective-embeddings/linear-series/embedded-curve-degree-compatibility.md` |
| Example 3.3.3 | `curves/projective-embeddings/linear-series/genus-one-very-ample-degree-three.md` |
| Example 3.3.4 | `curves/projective-embeddings/linear-series/genus-two-degree-five-embedding.md` |
| Secant and tangent incidence | `curves/projective-embeddings/linear-series/secant-tangent-incidence-api.md` |
| Proposition 3.4 | `curves/projective-embeddings/linear-series/projection-closed-immersion-criterion.md` |
| Secant dimension in Proposition 3.5 | `curves/projective-embeddings/linear-series/secant-incidence-dimension.md` |
| Tangent dimension in Proposition 3.5 | `curves/projective-embeddings/linear-series/tangent-variety-closed-dimension.md` |
| Proposition 3.5 | `curves/projective-embeddings/linear-series/projection-embedding-one-step.md` |
| Corollary 3.6 | `curves/projective-embeddings/linear-series/curve-embeds-projective-three-space.md` |
| Proposition 3.7 | `curves/projective-embeddings/linear-series/nodal-projection-local-criterion.md` |
| Bad secant loci | `curves/projective-embeddings/nodal-models/bad-multisecant-coplanar-tangent-loci.md` |
| Proposition 3.8(a) to (b) | `curves/projective-embeddings/nodal-models/multisecants-imply-coplanar-tangents.md` |
| Proposition 3.8(b) | `curves/projective-embeddings/nodal-models/coplanar-tangents-common-point.md` |
| Strange definition and examples | `curves/projective-embeddings/nodal-models/strange-curve-api.md` |
| Inseparability step in Theorem 3.9 | `curves/projective-embeddings/nodal-models/strange-projection-inseparable.md` |
| Hurwitz calculation in Theorem 3.9 | `curves/projective-embeddings/nodal-models/samuel-hurwitz-numerics.md` |
| Theorem 3.9 | `curves/projective-embeddings/nodal-models/samuel-strange-curve-classification.md` |
| Bad-center dimension bound | `curves/projective-embeddings/nodal-models/bad-center-dimension-bound.md` |
| Theorem 3.10 | `curves/projective-embeddings/nodal-models/nodal-projection-exists.md` |
| Corollary 3.11 | `curves/projective-embeddings/nodal-models/birational-nodal-plane-model.md` |
| Basic properties of `V_(d,r)` | `curves/projective-embeddings/nodal-models/severi-parameter-genus-extremes.md` |
| Harris–Severi theorem | `curves/projective-embeddings/nodal-models/harris-severi-theorem.md` |
| Exercise 3.4(b) | `curves/projective-embeddings/exercises/rational-normal-curve-minimal-degree.md` |
| Exercise 3.4(c),(d) | `curves/projective-embeddings/exercises/conic-cubic-low-degree-corollaries.md` |
| Exercise 3.6(a) | `curves/projective-embeddings/exercises/degree-four-curve-trichotomy.md` |
| Exercise 3.6(b) | `curves/projective-embeddings/exercises/elliptic-quartic-two-quadrics.md` |
| Exercise 3.9 | `curves/projective-embeddings/castelnuovo/general-plane-section-no-three-collinear.md` |
| I Exercise 3.14(a) | `curves/projective-embeddings/prerequisites/projection-from-point-morphism.md` |
| I Exercise 5.6(b) | `curves/projective-embeddings/prerequisites/ordinary-node-local-criterion.md` |
