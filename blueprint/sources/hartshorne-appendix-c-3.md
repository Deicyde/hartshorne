# Hartshorne Appendix C, section 3: ℓ-adic cohomology

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Appendix C, §3, printed pp.453–454.  Section 2's historical survey occupies
pp.451–452; it motivates étale cohomology but does not supply additional
formal claims for this source unit.

Let `X` be a finite-type scheme over an algebraically closed field `k` of
characteristic `p>=0`, and let `ell` be a prime different from `p`.  The
roadmap uses `H^i_et` when a distinction from Zariski, analytic, or singular
cohomology is needed.

## Historical boundary, printed pp.451–452

Hartshorne recalls coherent, Witt-vector, `p`-adic, crystalline, and étale
approaches to the Weil conjectures, the standard conjectures, and the status
before Deligne's proof.  These are historical context.  In particular, the
1977 assertion that finite-dimensionality for nonproper `X` lacked a proof is
not adopted as a current mathematical proposition.  A modern roadmap may
strengthen proper finiteness, but only under an explicitly later source.

## Definition and coefficients (printed p.453)

The small étale site has objects étale over `X` and jointly surjective étale
covering families.  For the constant torsion sheaves `Z/ell^r Z`, define
torsion étale cohomology by derived global sections.  Put

`Z_ell = inverse-limit_r Z/ell^r Z`

and let `Q_ell` be its fraction field.  Hartshorne defines

`H^i(X,Q_ell) = (inverse-limit_r H^i_et(X,Z/ell^r Z)) tensor_(Z_ell) Q_ell`.

This is the source-shaped classical definition.  A formal implementation
must record the transition maps and compare the ordinary inverse limit with
derived or pro-étale `ell`-adic cohomology; possible `lim^1` terms must not be
silently discarded.

## Properties 3.1 through 3.5 (printed p.453)

- **3.1.**  `H^i(X,Q_ell)` is a `Q_ell`-vector space and vanishes outside
  `0<=i<=2 dim X`.  Hartshorne records finite-dimensionality for proper `X`.
- **3.2.**  It is contravariantly functorial in `X`.
- **3.3.**  It has natural cup products
  `H^i times H^j -> H^(i+j)`.
- **3.4.**  If `X` is connected, smooth, and proper of dimension `n`, top
  cohomology is one-dimensional and complementary cup-product pairings are
  perfect.
- **3.5.**  If `X` is smooth proper and `f:X->X` has isolated fixed points
  with `1-df_x` invertible at each fixed point, then every local term is one
  and

  `#Fix(f)=sum_i (-1)^i Tr(f^*|H^i(X,Q_ell))`.

Hartshorne suppresses Tate twists.  The formal Poincaré statement is

`H^i(X,Q_ell) times H^(2n-i)(X,Q_ell(n)) -> Q_ell`

after cup product and the trace
`H^(2n)(X,Q_ell(n))->Q_ell`.  Equivalently untwisted top cohomology is
`Q_ell(-n)`.  This correction is essential for Frobenius actions.

The fixed-point differential condition is scheme-theoretic transversality of
the graph and diagonal.  Set-theoretic isolation alone does not make a fixed
point multiplicity one.

## Properties 3.6 through 3.8 (printed p.454)

- **3.6.**  For a smooth proper morphism `f:X->Y`, torsion proper-smooth base
  change and lissity of `R^i f_*` make geometric-fibre dimensions locally
  constant; they are constant for connected `Y`.  In particular dimensions
  are invariant under algebraically closed base-field extension.
- **3.7.**  For smooth proper `X/C`, étale and classical cohomology compare.
  The canonical starting point is

  `H^i_et(X,Z/ell^r) ~= H^i_sing(X^h,Z/ell^r)`.

  Passing to `Z_ell` and `Q_ell` gives the canonical `ell`-adic comparison.
  Hartshorne's displayed tensor product with `C` additionally requires a
  chosen abstract embedding `Q_ell->C`; it is not canonical.
- **3.8.**  For connected smooth proper `X` and a codimension-`q` integral
  subvariety `Z`, the modern cycle class lies in

  `H^(2q)(X,Q_ell(q))`.

  It is additive, invariant under rational equivalence, carries Chow
  intersection to cup product, and gives a graded map

  `A^*(X) -> direct-sum_q H^(2q)(X,Q_ell(q))`.

  The class of a closed point is nonzero; with the standard trace
  normalization a degree-one point has trace one.

The Tate twists, trace, purity/Gysin construction, and geometric-fibre
language are explicit roadmap requirements even though Hartshorne suppresses
them in the survey.

## Downstream use

- Appendix C §4 uses finite-dimensionality, contravariance, and the Lefschetz
  formula to express Frobenius point counts as alternating traces and prove
  zeta rationality.
- The functional equation uses cup-product naturality, the top-degree
  Frobenius action, and Poincaré duality.
- Smooth proper base change and complex comparison identify the resulting
  dimensions with classical Betti numbers under lifting and reduction.
- The cycle-class map feeds the standard-conjecture and homological-
  equivalence discussion and depends on the Appendix A Chow ring.

Hartshorne's `q`-power point map is fixed in the §4 roadmap.  Sources using
the opposite arithmetic/geometric Frobenius convention must have eigenvalues
and Tate twists translated consistently.

## Proof sources and blockers

Use exact passages from SGA 4 for the étale site, torsion cohomology, cup
products, and base change; SGA 4½ or a modern finiteness source for
constructibility and finite-dimensionality; and SGA 5 for trace, Poincaré
duality, Lefschetz, and cycle classes.  Artin comparison or a modern theorem
is required for 3.7.  Purity/Gysin should use a precise modern source.

Hartshorne omits twisted coefficients, constructible/lisse sheaves, higher
direct images, Leray, compact support, and derived inverse limits.  Several
displayed properties cannot be formalized honestly without adding the
relevant portions of that infrastructure.

## Pinned Mathlib audit

The pinned checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`).  A temporary Lean
check verified these exact declarations:

- `AlgebraicGeometry.Scheme.smallEtaleTopology`;
- `AlgebraicGeometry.Scheme.smallEtalePretopology`;
- `AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff`;
- `PadicInt` and `Padic` (`Z_[ell]` and `Q_[ell]` notation);
- `AlgebraicGeometry.Scheme.ellAdicSheaf`;
- `AlgebraicGeometry.Scheme.EllAdicCohomology`.

Only the small-étale-site leaf is an exact whole-leaf match.  The last two
declarations define pro-étale `Z_ell` cohomology in a larger universe.  Their
source file explicitly says comparison with the classical definition is
future work.  They do not provide Hartshorne's rational `Q_ell` groups,
finiteness, cup products, duality, trace, comparison, or cycle classes.

## Representation warnings and omission risks

- Keep small étale, big étale, and pro-étale sites distinct.
- Require `ell` invertible on the base; no `ell=p` specialization is allowed.
- Compare naive inverse limits with derived/pro-étale cohomology and expose
  `lim^1` obligations.
- Keep ordinary and compactly supported cohomology distinct for nonproper
  schemes.
- Include connectedness in the one-dimensional top-cohomology statement.
- Restore Tate twists in duality, trace, and cycle classes.
- Use geometric fibres in base change.
- A simple fixed point requires invertibility of `1-df`, not only isolation.
- Make any embedding `Q_ell->C` an explicit noncanonical choice.
- Fix arithmetic versus geometric Frobenius orientation.
- Construct cycle classes through purity/Gysin and normalize the point trace.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Small étale site | `weil-conjectures/etale-cohomology/foundations/small-etale-site.md` |
| Constant torsion sheaf | `weil-conjectures/etale-cohomology/foundations/constant-torsion-etale-sheaf.md` |
| Torsion étale cohomology | `weil-conjectures/etale-cohomology/foundations/torsion-etale-cohomology.md` |
| `Z_ell` and `Q_ell` | `weil-conjectures/etale-cohomology/foundations/ell-adic-integers-and-field.md` |
| Classical inverse system | `weil-conjectures/etale-cohomology/foundations/classical-ell-adic-inverse-system.md` |
| Classical/pro-étale comparison | `weil-conjectures/etale-cohomology/foundations/classical-proetale-ell-adic-comparison.md` |
| Rational ℓ-adic cohomology | `weil-conjectures/etale-cohomology/foundations/rational-ell-adic-cohomology.md` |
| 3.1, vanishing range | `weil-conjectures/etale-cohomology/properties/ell-adic-vanishing-range.md` |
| 3.1, proper finiteness | `weil-conjectures/etale-cohomology/properties/proper-ell-adic-finite-dimensionality.md` |
| 3.2 | `weil-conjectures/etale-cohomology/properties/ell-adic-pullback-functoriality.md` |
| 3.3 | `weil-conjectures/etale-cohomology/properties/ell-adic-cup-product.md` |
| Tate twists | `weil-conjectures/etale-cohomology/properties/etale-tate-twist.md` |
| Top trace | `weil-conjectures/etale-cohomology/properties/top-cohomology-trace.md` |
| 3.4 | `weil-conjectures/etale-cohomology/properties/ell-adic-poincare-duality.md` |
| Simple fixed point | `weil-conjectures/etale-cohomology/properties/simple-fixed-point-transversality.md` |
| 3.5 | `weil-conjectures/etale-cohomology/properties/ell-adic-lefschetz-fixed-point.md` |
| Torsion smooth proper base change | `weil-conjectures/etale-cohomology/properties/torsion-smooth-proper-base-change.md` |
| Lisse higher direct image | `weil-conjectures/etale-cohomology/properties/smooth-proper-lisse-higher-direct-image.md` |
| 3.6, rank constancy | `weil-conjectures/etale-cohomology/properties/ell-adic-fiber-rank-constancy.md` |
| 3.6, field extension | `weil-conjectures/etale-cohomology/properties/ell-adic-base-field-invariance.md` |
| Torsion comparison | `weil-conjectures/etale-cohomology/comparison/etale-singular-torsion-comparison.md` |
| ℓ-adic singular comparison | `weil-conjectures/etale-cohomology/comparison/ell-adic-singular-comparison.md` |
| Hartshorne's complex comparison | `weil-conjectures/etale-cohomology/comparison/chosen-complex-coefficient-comparison.md` |
| Purity/Gysin | `weil-conjectures/etale-cohomology/cycle-classes/etale-purity-gysin-class.md` |
| Class of a subvariety | `weil-conjectures/etale-cohomology/cycle-classes/etale-cycle-class-of-subvariety.md` |
| Rational equivalence | `weil-conjectures/etale-cohomology/cycle-classes/etale-cycle-class-rational-equivalence.md` |
| Intersection/cup compatibility | `weil-conjectures/etale-cohomology/cycle-classes/etale-cycle-class-intersection-cup.md` |
| Chow-ring map | `weil-conjectures/etale-cohomology/cycle-classes/chow-to-ell-adic-cycle-class.md` |
| Closed-point nonvanishing | `weil-conjectures/etale-cohomology/cycle-classes/closed-point-etale-cycle-class-nonzero.md` |

## Reused prerequisite map

| Input | Existing roadmap article |
|---|---|
| Analytification | `transcendental-methods/analytification/analytification-functor.md` |
| Analytic derived cohomology | `transcendental-methods/analytification/analytic-derived-cohomology.md` |
| Chow groups | `intersection-theory/chow/cycles/chow-groups-graded.md` |
| Chow intersection | `intersection-theory/chow/product/intersection-product-existence.md` |
| Smooth morphisms | `cohomology/smooth-morphisms/criteria/smooth-iff-geometrically-regular-fibers.md` |
| Proper morphisms | `schemes/proper-and-projective/proper-morphism.md` |
