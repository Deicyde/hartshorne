# Hartshorne Appendix C, overview and section 1

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Appendix C overview and §1, printed pp.449–451. Section 2 begins on p.451 and
is outside this source unit. The overview records the historical conjectures
and their proofs; the roadmap treats the solved assertions as modern theorems
with explicit proof-source blockers, not as open conjectures.

## Historical status, printed p.449

Weil formulated the conjectures in 1949. Grothendieck's l-adic theory proved
rationality cohomologically, and Deligne proved the remaining weight/Riemann-
hypothesis assertion in 1973. Dwork supplied independent p-adic proofs of
rationality and the functional equation. These historical claims are context,
not separate formal theorem leaves.

## Point counts and the formal zeta series, printed pp.449–450

Let `k=F_q`, let `X` be a finite-type `k`-scheme, and put
`k_r=F_(q^r)`. Define

`N_r(X)=#X(k_r)`

scheme-theoretically as the cardinality of morphisms `Spec k_r -> X`. This
set is finite. The Hasse–Weil zeta function is first a rational formal power
series

`Z(X,t)=exp(sum_(r>=1) N_r(X)*t^r/r) in Q[[t]]`.

It is essential to distinguish this formal series from the rational function
which later represents it.

For `P^1`, `N_r=q^r+1` and formal logarithm/exponential summation gives

`Z(P^1,t)=1/((1-t)*(1-q*t))`.

## Modern Weil theorem package, printed pp.450–451

For the displayed `P_0` and `P_(2n)` formulas, assume `X/F_q` is smooth,
projective, pure of dimension `n`, and geometrically connected. Geometric
connectedness is necessary: without it `P_0` need not equal `1-t`.

Let

`E=deg(Delta_X.Delta_X)=deg c_n(T_X)`.

The second equality is Appendix A Exercise A.6.6.

The modern theorem package is:

1. **Rationality.** `Z(X,t)` is represented by an element of `Q(t)`.
2. **Factorization.** There are `P_i(t) in Z[t]` such that

   `Z(X,t)=product_(i odd) P_i(t) / product_(i even) P_i(t)`,

   with `P_0(t)=1-t` and `P_(2n)(t)=1-q^n*t`.
3. **Functional equation.** As rational functions,

   `Z(X,1/(q^n*t)) = +/- q^(n*E/2)*t^E*Z(X,t)`.
4. **Weights.** Each

   `P_i(t)=product_j (1-alpha_(i,j)*t)`,

   where the `alpha_(i,j)` are algebraic integers and every complex embedding
   has absolute value `q^(i/2)`.
5. **Betti consequences.** With `B_i=deg P_i`,

   `E=sum_i (-1)^i*B_i`.

The weight separation makes the `P_i` uniquely determined by the rational
zeta function once they exist.

Modern proofs use finite-dimensional l-adic cohomology, geometric Frobenius,
the Grothendieck–Lefschetz trace formula, Poincare duality, independence of
`l`, and Deligne purity. Appendix C §4 restates and deduces these final
theorem pages; that source unit supplies deduction leaves rather than
duplicating the theorem nodes below.

## Good-reduction comparison, printed p.451

Hartshorne's shorthand is formalized with a good-reduction hypothesis. Let a
smooth proper scheme over a localization of a number ring have special fibre
`X/F_q` and complex fibre `Y_C`. Then

`B_i(X)=rank_Z H^i(Y_C^h,Z)`.

An arbitrary reduction of an unrelated number-ring model is insufficient.
The proof requires smooth proper base change and l-adic/singular comparison.

## The projective-line verification, printed p.451

For `P^1`, `E=2` and

`Z(P^1,1/(q*t))=q*t^2*Z(P^1,t)`.

The middle polynomial is `P_1=1`, hence `B_0=B_2=1`, `B_1=0`, agreeing with
the ordinary Betti numbers of the Riemann sphere and with
`E=1-0+1=2`.

## Exercise disposition, printed pp.457–458

Exercises C.5.1–C.5.7 occur at the end of the appendix. There is no later
running text. Under the project's later-running-use rule they are OUT. In
particular C.5.2 is an optional extension of the running `P^1` calculation to
`P^n`, not a retained source dependency.

## Proof sources and blockers

Exact proof-level sources are required for:

- cohomological determinant factorization and rationality;
- integrality and l-independence of the `P_i`;
- Poincare-duality functional equation and its sign;
- Deligne's purity/weight theorem;
- the diagonal Euler number versus cohomological Euler characteristic;
- smooth-proper good-reduction comparison.

Suitable sources include SGA 4, SGA 4 1/2, SGA 5, SGA 7, Deligne's *Weil I*,
or a precise modern etale-cohomology text. Hartshorne's historical report is
not itself a proof specification.

## Pinned Mathlib audit

Pinned Mathlib supplies finite fields and formal-power-series infrastructure,
but no complete l-adic cohomology, Frobenius trace formula, Poincare duality,
Weil factorization, independence of `l`, or Deligne weights. No whole theorem
leaf in this package is an exact Mathlib result.

## Representation warnings

- Count scheme-valued rational points, not coordinate tuples.
- Keep the formal zeta series distinct from its rational representative.
- Preserve geometric connectedness for `P_0=1-t`.
- Interpret the functional equation in Laurent rational functions, including
  the sign and half-exponent notation.
- Quantify the weight absolute value over every complex embedding.
- Do not define `E` or `B_i` to be equal by fiat; relate them by a theorem.
- State the good-reduction model explicitly.
- Call the solved Weil assertions modern theorems while retaining the
  historical title in source prose.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Finite-field extension tower | `weil-conjectures/zeta/finite-field-extension-tower.md` |
| Finiteness of rational points | `weil-conjectures/zeta/finite-type-scheme-rational-points-finite.md` |
| Point-count sequence | `weil-conjectures/zeta/point-count-sequence.md` |
| Formal zeta series | `weil-conjectures/zeta/hasse-weil-zeta-formal-series.md` |
| Isomorphism invariance | `weil-conjectures/zeta/zeta-isomorphism-invariant.md` |
| `P^1` point count | `weil-conjectures/zeta/projective-line-point-count.md` |
| `P^1` zeta formula | `weil-conjectures/zeta/projective-line-zeta-function.md` |
| Weil hypotheses | `weil-conjectures/weil/geometrically-connected-smooth-projective-convention.md` |
| Diagonal Euler number | `weil-conjectures/weil/diagonal-euler-number.md` |
| Rationality | `weil-conjectures/weil/zeta-rationality.md` |
| Polynomial factorization | `weil-conjectures/weil/weil-polynomial-factorization.md` |
| Functional equation | `weil-conjectures/weil/zeta-functional-equation.md` |
| Deligne weights | `weil-conjectures/weil/deligne-weight-theorem.md` |
| Polynomial uniqueness | `weil-conjectures/weil/weil-polynomial-uniqueness.md` |
| Weil Betti numbers | `weil-conjectures/weil/weil-betti-numbers.md` |
| Euler/Betti identity | `weil-conjectures/weil/euler-number-alternating-betti-sum.md` |
| Good-reduction comparison | `weil-conjectures/weil/good-reduction-betti-comparison.md` |
| `P^1` Euler number | `weil-conjectures/examples/projective-line-diagonal-euler-number.md` |
| `P^1` functional equation | `weil-conjectures/examples/projective-line-functional-equation.md` |
| `P^1` Weil polynomials and Betti numbers | `weil-conjectures/examples/projective-line-weil-polynomials-betti.md` |

## Expected Appendix C §4 deduction map

| Deduction | Expected roadmap article |
|---|---|
| Frobenius determinant factorization | `weil-conjectures/deductions/frobenius-determinant-factorization.md` |
| Rationality over `Q` | `weil-conjectures/deductions/rationality-descends-to-q.md` |
| Cohomological Euler characteristic | `weil-conjectures/deductions/cohomological-euler-characteristic.md` |
| Functional equation from duality | `weil-conjectures/deductions/functional-equation-from-poincare-duality.md` |
| Deligne polynomial identification and weights | `weil-conjectures/deductions/deligne-polynomial-identification.md` |
