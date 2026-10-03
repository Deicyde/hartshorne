# Hartshorne V.1, geometry on a surface

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter V, §1, printed pp.357–368. The chapter introduction is on p.356;
§1 begins on p.357, its exercises occupy pp.366–368, and §2 begins on p.369.

Throughout Chapter V, a surface is a nonsingular projective surface over an
algebraically closed field. A curve on a surface means an effective divisor
and may be singular, reducible, or nonreduced. Points are closed points.

## The surface intersection pairing, printed pp.357–360

Two curves meet transversally at a point when their local equations generate
the maximal ideal of the regular local ring of the surface. Theorem 1.1 gives
the unique symmetric additive pairing

`Div X times Div X -> Z`, `(C,D) |-> C.D`,

which depends only on linear equivalence and counts intersection points for
smooth curves meeting transversally.

Lemma 1.2 is the simultaneous moving input: for finitely many irreducible
curves `C_i` and a very ample divisor `D`, a general member of `|D|` is
irreducible and nonsingular and meets every `C_i` transversally. Lemma 1.3
identifies the number of transverse intersections with
`deg_C(O_X(D)|_C)`.

Hartshorne first defines the pairing on the cone of very ample divisors and
then extends it after writing arbitrary divisors as differences of very ample
ones. Proposition 1.4 identifies it, for curves with no common irreducible
component, with the sum of the local lengths

`length_(O_(X,P))(O_(X,P)/(f,g))`.

## Self-intersection, examples, and adjunction, printed pp.360–362

For a smooth curve `C subset X`, Example 1.4.1 gives

`C^2=deg_C N_(C/X)`.

On `P^2`, the line class has square one and curves of degrees `m,n` have
intersection `m*n`, recovering Bézout. On a smooth quadric, the two ruling
classes have squares zero and mutual intersection one, so types `(a,b)` and
`(a',b')` intersect in `a*b'+a'*b`.

A canonical divisor represents `omega_X`; its square is an invariant of the
surface. It equals nine on `P^2` and eight on a smooth quadric. Proposition
1.5 is adjunction: for a smooth genus-`g` curve `C`,

`2*g-2=C.(C+K)`.

The plane-curve and quadric-curve genus formulas follow as Examples 1.5.1–2.

## Surface Riemann–Roch, printed pp.362–363

For a divisor `D`, Hartshorne writes `l(D)=dim H^0(X,O_X(D))`, calls
`s(D)=dim H^1(X,O_X(D))` the superabundance, and uses
`p_a(X)=chi(O_X)-1`. Theorem 1.6 states

`l(D)-s(D)+l(K-D) = D.(D-K)/2 + 1+p_a(X)`,

equivalently

`chi(O_X(D))=D.(D-K)/2+chi(O_X)`.

The proof moves `D` to a difference of smooth curves and combines the two
ideal sequences with additivity of Euler characteristic, curve
Riemann–Roch, and adjunction.

Remark 1.6.1 records the forward Hirzebruch–Riemann–Roch consequence

`12*(1+p_a(X))=K^2+c_2(X)`.

It is delegated to Appendix A, Theorem 4.1 and Example 4.1.2. Remark 1.6.2
uses Exercise 1.2 to identify intersection with a very ample divisor with
embedded degree; intersection with an ample divisor is positive on every
curve. Lemma 1.7 gives a bound `n_0` such that `D.H>n_0` implies
`H^2(X,O_X(D))=0`. Corollary 1.8 uses Riemann–Roch to show that if
`D.H>0` and `D^2>0`, then `nD` is effective for every sufficiently large
`n`.

## Numerical equivalence and the Hodge index theorem, printed p.364

A divisor is numerically zero when it intersects every divisor trivially;
`Num X` is the divisor-class group modulo numerical equivalence. Theorem 1.9
says that for an ample `H`, if `D` is not numerically zero and `D.H=0`, then
`D^2<0`.

Remark 1.9.1 invokes the Néron–Severi theorem to make `Num X` a finite-rank
free abelian group. Sylvester's law of inertia then identifies the real
intersection form as having one positive and all remaining negative
directions. Example 1.9.2 displays the diagonal form on a smooth quadric.

## Nakai–Moishezon, printed pp.365–366

Theorem 1.10 says that a divisor `D` on a Chapter-V surface is ample exactly
when `D^2>0` and `D.C>0` for every irreducible curve `C`.

For sufficiency, Corollary 1.8 first produces an effective multiple. The
restriction `O_X(D)|_D` is ample by reduction to the irreducible components
and their normalizations. Vanishing on `D` makes the dimensions of the
surface `H^1` groups stabilize, so high powers become globally generated.
The induced projective morphism has finite fibres, hence is finite by Stein
factorization, and pullback of `O(1)` is ample.

On a smooth quadric, a type `(a,b)` divisor is ample exactly when `a,b>0`.
Hartshorne also cites Mumford's example of a divisor positive on every
irreducible curve but with square zero, hence not ample.

## Exercise disposition, printed pp.366–368

- **Exercise 1.1 — OUT.** It polarizes Euler characteristics of the two
  associated invertible sheaves to recover `C.D`; no later running proof uses
  it.
- **Exercise 1.2 — ADOPTED.** It computes the quadratic Hilbert-polynomial
  coefficients from `H^2`, the genus of a smooth hyperplane curve, and
  `p_a(X)`, and identifies embedded degrees with intersection by `H`.
  Remark 1.6.2 and the Nakai proof use it.
- **Exercise 1.3(a,b) — ADOPTED; (c) OUT.** For an effective divisor,
  `2*p_a(D)-2=D.(D+K)`, and its arithmetic genus is invariant under linear
  equivalence. These clauses are used in V.3.7–3.8, V.4.8–4.9, and V.5.5.
  The virtual-genus identities of (c) have no later running use.
- **Exercise 1.4 — OUT.** The line-on-a-hypersurface self-intersection and
  characteristic-zero existence construction are not later dependencies.
  V.4.9 says only “see also” after deriving the line calculation independently.
- **Exercise 1.5(a) — ADOPTED; (b) OUT.** For a smooth degree-`d` surface in
  `P^3`, `K^2=d*(d-4)^2`; Appendix A, Example 4.1.3 uses it. The product-of-
  curves formula in (b) has no later running use.
- **Exercise 1.6(a) — ADOPTED; (b) OUT.** The diagonal calculation
  `Delta^2=2-2g` is required by the Weil argument in Exercise 1.10. The
  rank-three numerical-class calculation in (b) feeds only excluded
  Exercise 1.11.
- **Exercise 1.7(a–c) — ADOPTED.** Algebraically trivial divisors form a
  subgroup, linear equivalence implies algebraic equivalence, and algebraic
  equivalence implies numerical equivalence. V.2.1 uses (c), while Appendix B
  §5 uses the algebraic-equivalence and Néron–Severi framework.
- **Exercise 1.8(a) — ADOPTED; (b) OUT.** The `dlog` cohomology classes of
  divisors pair to their intersection number. V.5.8 uses this compatibility.
  The characteristic-zero finite-generation argument in (b) is not needed.
- **Exercise 1.9(a,b) — ADOPTED.** The Hodge-index inequality and its
  Castelnuovo–Severi specialization on a product of curves are the proof
  inputs cited in Appendix C §2.
- **Exercise 1.10 — ADOPTED.** Weil's Riemann-hypothesis bound for curves
  over finite fields is cited in Appendix C §2. Its later appearance in
  Appendix C Exercise 5.7 is exercise-only but does not alter the decision.
- **Exercises 1.11–1.12 — OUT.** They have no later included running-text
  dependency.

Exercise 1.8(a) reactivates exactly III Exercise 7.4(a,c,d): the point-trace
normalization, the `dlog` Picard class, and identification of a smooth
prime-divisor class. III Exercise 7.4(b), which uses Exercise 7.3 to calculate
classes in projective space, remains out.

## External sources and blockers

- The direct surface intersection pairing, surface Riemann–Roch, Hodge index,
  and Nakai–Moishezon have proofs in §1; their historical references are not
  separate blockers.
- Néron–Severi finite generation over an arbitrary algebraically closed field
  needs an adopted passage from Lang–Néron [1] or Hartshorne [6].
- Mumford's strictly-nef square-zero example needs the cited proof from
  Hartshorne [5], I.10.6.
- The Noether formula derives from the untagged, not-ready Appendix A
  Hirzebruch–Riemann–Roch prerequisite. Hartshorne cites Borel–Serre [1] for
  the algebraic theorem.

Thus there are two source-tagged V.1 blockers and one untagged forward
Appendix A blocker.

## Appendix A reconciliation

The §1 construction of the surface intersection pairing is direct and does
not depend on future Chow theory. Appendix A should later prove that its
product `A^1(X) times A^1(X) -> A^2(X)` agrees with this pairing. Only the
Noether formula points forward now, through Appendix A Hirzebruch–Riemann–
Roch. This direction avoids a rolled-up dependency cycle when Appendix A
uses the V.1 pairing and Riemann–Roch theorem as motivating base cases.

## Pinned Mathlib audit and false friends

The pinned checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). The exact whole-
leaf overlap is the real-linear-algebra theorem of Sylvester:
`QuadraticForm.equivalent_one_neg_one_weighted_sum_squared`, together with
`sigPos_of_equiv_weightedSumSquares` and
`sigNeg_of_equiv_weightedSumSquares`. It supplies only the final signature
step after the finite-dimensional numerical divisor space and its intersection
form have been constructed.

`AlgebraicGeometry.AlgebraicCycle`, added in pinned Mathlib in June 2026,
defines locally finite cycles and a weighted pushforward for quasicompact
morphisms. It has no rational equivalence, Chow group, or intersection
product. `CommRing.Pic` is the Picard group of a ring and explicitly lacks the
scheme/invertible-sheaf/`H^1(O^*)` bridge. `Polynomial.hilbertPoly`, the
homological Euler-characteristic API, module length, and the ell-adic-site
files do not supply the corresponding geometric theorems.

There is no exact pinned theorem for the surface divisor pairing, local-to-
global intersection formula, adjunction, surface Riemann–Roch, the Noether
formula, numerical or algebraic equivalence, Hodge index, Néron–Severi,
Nakai–Moishezon, or the divisor cohomology class. No other V.1 leaf should be
marked as supplied by Mathlib.

## Representation choices

- Represent divisors by the existing project Weil-divisor API, using
  regularity to pass through locally factorial Cartier divisors and the
  Picard group. The pairing is an integer-valued symmetric biadditive map and
  factors through linear equivalence.
- Use effective Cartier divisors and their associated closed subschemes for
  local intersections; the local multiplicity is module length in the regular
  surface local ring.
- Define `Num X` as the quotient by the radical of the intersection pairing.
  Do not assume finite rank until the Néron–Severi blocker is discharged.
- State surface Riemann–Roch first as an Euler-characteristic identity; derive
  the classical `l-s+l` display using Serre duality.
- Define algebraic equivalence as the transitive closure of fibrewise
  equivalence in flat Cartier-divisor families. Do not silently assume the
  one-family relation is transitive.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Chapter-V surface and curve conventions | `surfaces/intersection-theory/foundations/surface-curve-convention.md` |
| Transverse curve intersections | `surfaces/intersection-theory/foundations/transverse-curve-intersection.md` |
| Lemma 1.2 | `surfaces/intersection-theory/foundations/simultaneous-bertini-moving.md` |
| Lemma 1.3 | `surfaces/intersection-theory/foundations/transverse-intersection-restriction-degree.md` |
| Pairing on very ample divisors | `surfaces/intersection-theory/foundations/very-ample-intersection-pairing.md` |
| Theorem 1.1 | `surfaces/intersection-theory/foundations/divisor-intersection-pairing.md` |
| Local intersection multiplicity | `surfaces/intersection-theory/foundations/local-intersection-multiplicity.md` |
| Proposition 1.4 | `surfaces/intersection-theory/foundations/intersection-number-sum-local-lengths.md` |
| Example 1.4.1 | `surfaces/intersection-theory/foundations/self-intersection-normal-bundle-degree.md` |
| Example 1.4.2 | `surfaces/intersection-theory/examples-adjunction/projective-plane-intersection-form.md` |
| Example 1.4.3 | `surfaces/intersection-theory/examples-adjunction/quadric-surface-intersection-form.md` |
| Example 1.4.4 | `surfaces/intersection-theory/examples-adjunction/canonical-divisor-self-intersection.md` |
| Proposition 1.5 | `surfaces/intersection-theory/examples-adjunction/surface-curve-adjunction.md` |
| Example 1.5.1 | `surfaces/intersection-theory/examples-adjunction/plane-curve-genus-adjunction.md` |
| Example 1.5.2 | `surfaces/intersection-theory/examples-adjunction/quadric-curve-genus-adjunction.md` |
| Surface Euler characteristic and superabundance | `surfaces/numerical-positivity/surface-riemann-roch/surface-euler-superabundance.md` |
| Difference-of-curves calculation | `surfaces/numerical-positivity/surface-riemann-roch/surface-rr-difference-of-curves.md` |
| Theorem 1.6 | `surfaces/numerical-positivity/surface-riemann-roch/surface-riemann-roch.md` |
| Positivity of ample intersection degree | `surfaces/numerical-positivity/surface-riemann-roch/ample-intersection-degree-positive.md` |
| Lemma 1.7 | `surfaces/numerical-positivity/surface-riemann-roch/surface-h2-vanishing-bound.md` |
| Corollary 1.8 | `surfaces/numerical-positivity/surface-riemann-roch/positive-square-eventual-effectivity.md` |
| Remark 1.6.1, Noether formula | `surfaces/numerical-positivity/surface-riemann-roch/noether-formula.md` |
| Numerical equivalence and `Num X` | `surfaces/numerical-positivity/hodge/numerical-equivalence-num.md` |
| Theorem 1.9 | `surfaces/numerical-positivity/hodge/hodge-index-negative-complement.md` |
| Néron–Severi theorem | `surfaces/numerical-positivity/hodge/neron-severi-finite-generation.md` |
| Sylvester's law of inertia | `surfaces/numerical-positivity/hodge/sylvester-law-inertia.md` |
| Remark 1.9.1 and Example 1.9.2 | `surfaces/numerical-positivity/hodge/hodge-signature-quadric.md` |
| Necessity in Theorem 1.10 | `surfaces/numerical-positivity/nakai/nakai-necessity.md` |
| Ampleness on the effective divisor | `surfaces/numerical-positivity/nakai/ample-restriction-effective-divisor.md` |
| Stabilization and global generation | `surfaces/numerical-positivity/nakai/h1-stabilization-global-generation.md` |
| The associated morphism is finite | `surfaces/numerical-positivity/nakai/globally-generated-morphism-finite.md` |
| Theorem 1.10 | `surfaces/numerical-positivity/nakai/nakai-moishezon-surface.md` |
| Quadric ample cone | `surfaces/numerical-positivity/nakai/quadric-ample-cone.md` |
| Mumford strictly-nef counterexample | `surfaces/numerical-positivity/nakai/mumford-strictly-nef-counterexample.md` |
| Exercise 1.2 | `surfaces/surface-exercises/surface-hilbert-polynomial-intersection-coefficients.md` |
| Exercise 1.3(a,b) | `surfaces/surface-exercises/effective-divisor-arithmetic-genus-adjunction.md` |
| Exercise 1.5(a) | `surfaces/surface-exercises/projective-hypersurface-canonical-self-intersection.md` |
| Exercise 1.7(a,b) | `surfaces/equivalence-exercises/algebraic-equivalence-subgroup-linear.md` |
| Exercise 1.7(c) | `surfaces/equivalence-exercises/algebraic-equivalence-implies-numerical.md` |
| Exercise 1.8(a) | `surfaces/surface-exercises/divisor-cohomology-class-intersection.md` |
| Exercise 1.9(a) | `surfaces/surface-exercises/hodge-index-cauchy-schwarz.md` |
| Exercise 1.9(b) | `surfaces/surface-exercises/castelnuovo-severi-product-inequality.md` |
| Exercise 1.6(a) and 1.10 | `surfaces/surface-exercises/weil-riemann-hypothesis-curves.md` |
| III Exercise 7.4(c) prerequisite | `surfaces/prerequisites/dlog-picard-cohomology-class.md` |
| III Exercise 7.4(a,d) prerequisite | `surfaces/prerequisites/codimension-one-cohomology-class-point-trace.md` |
| Forward Appendix A HRR prerequisite | `surfaces/prerequisites/surface-noether-formula-hrr.md` |
