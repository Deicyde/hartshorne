# Hartshorne Appendix C §4, cohomological interpretation of the Weil conjectures

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Appendix C, §4. The running text occupies printed pp.454–457. Exercises
5.1–5.4 begin on p.457 and Exercises 5.5–5.7 finish on p.458. The bibliography
begins on p.459; there is no continuation.

Section 4 derives rationality and the functional equation formally from the
ℓ-adic package of §3, then quotes Deligne's purity theorem to finish the Weil
conjectures. The final conjecture statements themselves belong to the §1
roadmap; this source note maps twenty §4 proof-architecture and deduction
leaves.

## Frobenius and the trace formula, printed p.454

Let `X/F_q` be projective and let `X_bar` be its base change to the algebraic
closure. Hartshorne uses the endomorphism whose action on geometric points is

`(a_i) |-> (a_i^q)`.

He calls this the `k`-linear Frobenius after identifying the `q`-twist with
`X_bar`. Sources differ on whether this or its inverse is called geometric
Frobenius; the roadmap calls it Hartshorne's `q`-power Frobenius, fixes the
point-action convention, and adjusts Tate twists and eigenvalues consistently.

The fixed points of `F^r` are exactly the `F_(q^r)`-rational points, so

`N_r=#Fix(F^r)`.

For smooth `X`, Frobenius fixed points are simple: its tangent map is zero, so
`1-dF^r` is invertible. The ℓ-adic Lefschetz formula therefore gives

`N_r=sum_i (-1)^i Tr((F^r)^*|H^i(X_bar,Q_ell))`.

The `q`-power Frobenius is a finite universal homeomorphism. Its pullback is
therefore an automorphism of torsion and ℓ-adic cohomology; this is needed
later to identify the degree of each determinant polynomial with the full
cohomology dimension.

Substitution into the logarithm of the zeta series expresses `log Z(X,t)` as
the alternating sum of Frobenius trace-power series.

## Determinant factorization and rationality, printed p.455

Lemma 4.1 is the finite-dimensional formal identity

`exp(sum_(r>=1)Tr(phi^r)t^r/r)=det(1-t*phi)^(-1)`.

For

`P_i(t)=det(1-tF^*|H^i(X_bar,Q_ell))`,

Theorem 4.2 gives

`Z(X,t)=prod_i P_i(t)^((-1)^(i+1))`.

This first proves rationality over `Q_ell`. Since the defining power series
has rational coefficients, Hartshorne invokes

`Q[[t]] intersect Q_ell(t)=Q(t)`

to descend rationality to `Q`; the cited source is Bourbaki, Algebra IV §5,
Exercise 3.

## Linear algebra lemmas, printed pp.455–456

Lemma 4.1 is used over the characteristic-zero field `Q_ell`, where the
formal denominators and exponential are defined. Besides Lemma 4.1, Lemma
4.3 treats a perfect pairing `V times W -> K`, a nonzero scalar `A`, and
endomorphisms scaled by `A`. It identifies the endomorphism on one factor as
the scaled contragredient of the other and relates their characteristic
determinants. This is the linear-algebra input for Poincaré reciprocity.

## Extreme cohomology and Euler characteristic, printed p.456

Frobenius acts trivially in degree zero, so `P_0(t)=1-t`. On normalized top
cohomology it acts by `q^n`, yielding `P_(2n)(t)=1-q^n*t` for an `n`-fold.

Hartshorne provisionally defines

`B_i=dim_(Q_ell)H^i(X_bar,Q_ell)`

and the cohomological Euler characteristic `sum_i(-1)^iB_i`. Compatibility of
cycle classes, diagonal self-intersection, and Poincaré duality identifies this
with the diagonal invariant used in the functional equation. The omitted
intermediate input is the ℓ-adic Künneth theorem: under Künneth and duality,
the diagonal class is the graded coevaluation element, whose supertrace is
the alternating cohomology dimension.

Smooth-proper base change, algebraically closed base-field invariance, and the
ℓ-adic/singular comparison identify these dimensions with the topological
Betti numbers for a smooth proper model over a localization of a number ring,
with the finite-field and complex varieties as fibres.

## Functional equation, printed pp.456–457

Theorem 4.4 applies Lemma 4.3 to the Tate-twisted Poincaré pairings

`H^i times H^(2n-i)(n) -> Q_ell`.

Cup-product compatibility and the top-degree Frobenius normalization relate
the pairing by `<F^*v,F^*w>=q^n<v,w>` and hence relate `P_i` and
`P_(2n-i)`. Substitution in the determinant factorization proves the Weil
functional equation, with the Euler-characteristic exponent and determinant
sign retained explicitly.

Thus rationality, the functional equation, and the Betti/Euler comparison are
formal consequences of the §3 cohomological package and the §4 determinant
interpretation.

## Formal consequences and Deligne, printed p.457

Theorem 4.5 quotes Deligne's solution of the remaining conjecture. Every
`P_i(t)` has integer coefficients independent of `ell`, and its reciprocal
roots are algebraic integers whose complex absolute values are `q^(i/2)` for
every chosen embedding into `C`.

The cohomological purity statement says that every eigenvalue of Frobenius on
`H^i` has weight `i`. Together with integrality and ℓ-independence, this
identifies the cohomological determinant polynomials with the final, uniquely
determined integer polynomials in the Weil theorem and identifies their
degrees with the Betti numbers. The §4 purity leaf is the cohomological input;
the §1 weight leaf is the final theorem after this identification.

Hartshorne does not describe the proof. He points to SGA4, SGA5, and SGA7 and
mentions Lefschetz pencils, singular fibres, and monodromy. The roadmap keeps
the proof architecture separate from the Deligne theorem statement.

## Exercise disposition, printed pp.457–458

- **Exercises 5.1–5.4 — OUT.** Multiplicativity under stratification,
  projective-space examples, the affine-line product formula, and the
  arithmetic zeta comparison are not used by later included text.
- **Exercise 5.5 — OUT.** The finite determination of curve point counts is an
  optional consequence of the conjectures.
- **Exercise 5.6 — OUT.** The elliptic-curve calculation depends on excluded
  IV Exercise 4.16 and is not used later.
- **Exercise 5.7 — OUT.** It rederives the curve Riemann hypothesis from the
  already-adopted V Exercise 1.10, but has no later consumer.

There are no later exercises or running sections after p.458.

## External sources and blockers

The §4 formal deductions reuse the §3 source roots for finite-dimensional
ℓ-adic cohomology, functoriality, cup products, Tate twists, Poincaré duality,
simple fixed points, the Lefschetz trace formula, smooth-proper base change,
Artin comparison, and cycle classes.

The exact sources are SGA4 for torsion étale cohomology, SGA5 for ℓ-adic
passage and trace/cycle formalism, and SGA7 for Lefschetz pencils and
monodromy. Bourbaki supplies the rational-coefficient descent lemma.

The five explicit §4 blocker leaves are universal-homeomorphism invariance of
Frobenius pullback, the ℓ-adic Künneth/diagonal theorem, Deligne's
integrality/ℓ-independence theorem, Deligne purity on cohomology, and the
Lefschetz-pencil/monodromy proof architecture. The Deligne leaves are sourced
by “La conjecture de Weil I,” *Publ. Math. IHÉS* 43 (1974), together with
SGA7. Other blocked status is inherited from §3.

## Pinned Mathlib audit and false friends

The pinned checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). No §4 leaf is an
exact pinned-Mathlib result.

`Scheme.EllAdicCohomology` defines pro-étale `Z_ell` sheaf cohomology and
explicitly notes that comparison with classical étale cohomology and
smallness are future work. It supplies none of the finite-dimensional
`Q_ell`, cup-product, Poincaré-duality, trace, smooth-base-change, or
Frobenius properties used here.

`WeierstrassCurve.LFunction` is a number-field Euler product, not the
finite-field scheme zeta function. Arithmetic, Riemann, and Dedekind zeta
APIs are unrelated. Frobenius ring maps and determinant/trace primitives are
infrastructure only.

## Representation choices and warnings

- Fix arithmetic-versus-geometric Frobenius conventions at the point action,
  cohomological pullback, Tate twist, and reciprocal-root levels.
- Define `P_i(t)` as `det(1-tF^*)`, not with the inverse convention.
- Prove fixed points simple before replacing Lefschetz multiplicity by set
  cardinality.
- Separate rationality over `Q_ell` from descent to `Q(t)`.
- Normalize top cohomology and Frobenius degree consistently with Poincaré
  duality.
- State the chosen embeddings into `C` in the weight conclusion.
- Do not duplicate §1 final Weil-conjecture pages; §4 leaves feed them.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Hartshorne q-power Frobenius | `weil-conjectures/frobenius/finite-field-geometric-frobenius.md` |
| Frobenius pullback automorphism | `weil-conjectures/frobenius/frobenius-pullback-cohomology-automorphism.md` |
| Frobenius iterates and rational points | `weil-conjectures/frobenius/frobenius-iterate-fixed-points.md` |
| Simplicity of Frobenius fixed points | `weil-conjectures/frobenius/frobenius-fixed-points-simple.md` |
| Point-count trace formula | `weil-conjectures/frobenius/frobenius-point-count-trace-formula.md` |
| Zeta logarithm trace series | `weil-conjectures/frobenius/zeta-logarithm-trace-series.md` |
| Lemma 4.1 | `weil-conjectures/linear-algebra/trace-exponential-determinant-identity.md` |
| Lemma 4.3 | `weil-conjectures/linear-algebra/scaled-perfect-pairing-determinant-identity.md` |
| Theorem 4.2 | `weil-conjectures/deductions/frobenius-determinant-factorization.md` |
| Rationality descends to Q | `weil-conjectures/deductions/rationality-descends-to-q.md` |
| Extreme polynomials | `weil-conjectures/deductions/extreme-frobenius-polynomials.md` |
| Cohomological Euler characteristic | `weil-conjectures/deductions/cohomological-euler-characteristic.md` |
| ℓ-adic Künneth and diagonal coevaluation | `weil-conjectures/deductions/ell-adic-kunneth-diagonal.md` |
| Diagonal/Euler comparison | `weil-conjectures/deductions/diagonal-euler-trace-comparison.md` |
| Theorem 4.4 | `weil-conjectures/deductions/functional-equation-from-poincare-duality.md` |
| Smooth-proper Betti comparison | `weil-conjectures/deductions/smooth-proper-betti-comparison.md` |
| Deligne integrality and independence | `weil-conjectures/deductions/deligne-integrality-independence.md` |
| Deligne purity and weights | `weil-conjectures/deductions/deligne-purity-weights.md` |
| Weil-polynomial identification | `weil-conjectures/deductions/deligne-polynomial-identification.md` |
| Lefschetz-pencil proof architecture | `weil-conjectures/deductions/lefschetz-pencil-monodromy-proof-architecture.md` |
