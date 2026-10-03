# Hartshorne V.6, classification of surfaces

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter V, §6. The running survey occupies printed pp.421–422. Exercises
6.1–6.2 are wholly on p.423. Appendix A begins on p.424; there is no further
Chapter-V continuation or exercise.

This section is a classification survey. Hartshorne gives definitions and
short deductions, but quotes the major surface-classification theorems. Every
quoted theorem therefore needs a precise proof source rather than treating the
survey paragraph as a proof specification.

## Classification setting and historical disposition, printed p.421

The curve-classification recap reuses Chapter IV: unique smooth projective
models, genus, and moduli. For surfaces, smooth projective models are not
unique; the relatively minimal and minimal-model results are supplied by V.5.
The invariants `p_a` and `p_g` are birational, while `K^2` is attached to a
chosen minimal model.

Hartshorne's statements that the possible triples `(p_a,p_g,K^2)` were not
known and that moduli were “wide open except in special cases” describe the
state of the subject in 1977. They are historical context, not timeless
formal propositions.

## Canonical ring and Kodaira dimension, printed pp.421–422

For a projective variety `X`, define its canonical section ring

`R(X,K)=direct-sum_(n>=0) H^0(X,O_X(nK))`.

The Kodaira dimension is `trdeg_k R(X,K)-1`; it is `-1` when every positive
pluricanonical system is empty. It is a birational invariant. Equivalently,
when it is nonnegative, it is the maximum dimension of an image of a
pluricanonical rational map.

For an `n`-dimensional variety, every value from `-1` to `n` occurs. For a
smooth projective curve,

- `kappa=-1` exactly in genus zero;
- `kappa=0` exactly in genus one;
- `kappa=1` exactly in genus at least two.

The representation must distinguish an empty `|mK|` from a zero-dimensional
nonempty complete system.

## Kodaira dimension minus one, printed p.422

Theorem 6.1 states

`kappa(X)=-1 <-> |12K_X| is empty <-> X is rational or ruled`.

Both the fixed-twelve pluricanonical criterion and the rational/ruled
classification are quoted classification inputs.

Theorem 6.2 is Castelnuovo's rationality criterion:

`X is rational <-> p_a(X)=0 and P_2(X)=0`,

where `P_2=dim H^0(X,O_X(2K_X))`. Hartshorne cites Kodaira's complex proof
through Serre [13], and Zariski's proof in positive characteristic.

Remark 6.2.1 gives the separable surface analogue of Lüroth: if

`k subset L subset k(t,u)`

and `k(t,u)/L` is finite separable, then `L` is purely transcendental over
`k`. The proof descends geometric genus, irregularity, and the second
plurigenus to a smooth projective model of `L`, then applies Castelnuovo.
Without separability the conclusion is false; Hartshorne cites Zariski and
Shioda for the counterexample.

## Kodaira dimension zero, printed p.422

Theorem 6.3 states `kappa(X)=0` exactly when `12K_X` is linearly trivial.
Assuming `char k != 2,3`, the possibilities are exhausted by:

1. K3 surfaces: `K_X~0`, `q=0`, and `p_a=p_g=1`;
2. Enriques surfaces: `p_a=p_g=0`, `2K_X~0`;
3. abelian surfaces: `p_a=-1`, `p_g=1`;
4. hyperelliptic surfaces, with the elliptic-pencil structure described by
   Hartshorne.

Here “hyperelliptic surface” is the classical surface type, not a
hyperelliptic curve. The characteristic restriction is part of the adopted
statement; small-characteristic quasi-hyperelliptic and exceptional behaviour
must not be silently folded into it.

## Kodaira dimension one, printed p.422

Under `char k != 2,3`, Theorem 6.4 says that every Kodaira-dimension-one
surface is an elliptic surface: it admits a morphism to a smooth curve whose
fibres over a dense open are smooth genus-one curves. Hartshorne does not state
the converse here. No section is included in the definition. The theorem is
quoted without proof.

## Kodaira dimension two, printed p.422

Theorem 6.5 states that `kappa(X)=2` exactly when some positive
pluricanonical system determines a birational morphism onto its image. These
are the surfaces of general type. Hartshorne supplies neither a proof nor an
effective pluricanonical multiple.

## Exercise disposition, printed p.423

- **Exercise 6.1 — OUT.** It classifies which smooth complete-intersection
  surfaces are of general type. No later Appendix running text uses it.
- **Exercise 6.2 — OUT.** The Chern–Griffiths geometric-genus bound for a
  surface in projective space is not cited by later included running text.

There are no further Chapter-V exercises after 6.2.

## Proof sources and blockers

Hartshorne's general references are Bombieri–Husemoller,
“Classification and embeddings of surfaces,” *Proc. Symp. Pure Math.* 29
(1975), 329–420, and Shafarevich, *Algebraic Surfaces*.

The precise source obligations are:

- the Iitaka-dimension comparison between canonical-ring transcendence degree
  and maximal pluricanonical image dimension, and the realization of every
  value `-1,...,dim X`;
- the fixed-`12K` criterion and rational/ruled classification for
  `kappa=-1`;
- Castelnuovo rationality, sourced over `C` by Serre [13] and in positive
  characteristic by Zariski [5], [6], [9];
- separable descent and the surface-Lüroth theorem, plus Shioda's inseparable
  counterexample, including the characteristic-aware Picard/Albanese input
  for irregularity;
- `12K` torsion and exhaustive `kappa=0` classification under
  `char k != 2,3`, together with abelian-surface cohomology and finite-quotient
  descent for the type data;
- the `kappa=1` elliptic-surface classification under the same restriction;
- the `kappa=2` pluricanonical birationality theorem.

The roadmap isolates thirteen explicit blocker leaves after splitting these
packages into PR-sized claims. Exact characteristic-aware theorem passages
must be adopted; a generic survey citation is not sufficient.

## Pinned Mathlib audit and false friends

The pinned checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). No V.6 leaf is an
exact pinned-Mathlib result.

Pinned Mathlib has no canonical section ring or Kodaira dimension of a
variety, plurigenus, K3 or Enriques surface, abelian-surface classification,
hyperelliptic/bielliptic surface, elliptic-surface classification, surface of
general type, or Castelnuovo rationality theorem.

`FieldTheory.RatFunc.Luroth` is the one-variable Lüroth theorem and is a false
friend for the separable dimension-two surface theorem. Abelian-group and
abelian-scheme primitives do not provide the classification or numerical
invariants of abelian surfaces.

## Representation choices and warnings

- Define `kappa` from the graded canonical section ring with the explicit
  `-1` convention; do not use an unsigned dimension type that loses it.
- Package pluricanonical rational maps independently of a chosen basis and
  distinguish rational maps from everywhere-defined morphisms.
- Kodaira dimension is birational; `K^2` is stated only after choosing a
  minimal model.
- Keep `|mK|=empty` distinct from a system of projective dimension zero.
- Preserve `char k != 2,3` in the `kappa=0,1` classification leaves.
- Treat Hartshorne's historical moduli and “unknown triples” prose as context,
  not proof obligations.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Canonical section ring | `surfaces/numerical-classification/kodaira/canonical-section-ring.md` |
| Section-ring function-field embedding | `surfaces/numerical-classification/kodaira/canonical-ring-function-field-embedding.md` |
| Kodaira dimension | `surfaces/numerical-classification/kodaira/kodaira-dimension.md` |
| Canonical rings under birational isomorphism | `surfaces/numerical-classification/kodaira/canonical-ring-birational-isomorphism.md` |
| Birational invariance | `surfaces/numerical-classification/kodaira/kodaira-dimension-birational-invariant.md` |
| Pluricanonical rational-map interface | `surfaces/numerical-classification/kodaira/pluricanonical-rational-map-image-api.md` |
| Pluricanonical-image characterization | `surfaces/numerical-classification/kodaira/pluricanonical-image-characterization.md` |
| Range of Kodaira dimension | `surfaces/numerical-classification/kodaira/kodaira-dimension-range-realization.md` |
| Positive-degree curve section-ring transcendence degree | `surfaces/numerical-classification/kodaira/positive-degree-curve-section-ring-trdeg.md` |
| Curve trichotomy | `surfaces/numerical-classification/kodaira/curve-kodaira-dimension-trichotomy.md` |
| `kappa=-1` and `|12K|` | `surfaces/numerical-classification/kappa-minus-one/kappa-minus-one-p12-criterion.md` |
| Rational/ruled classification | `surfaces/numerical-classification/kappa-minus-one/kappa-minus-one-rational-ruled-classification.md` |
| Castelnuovo criterion | `surfaces/numerical-classification/kappa-minus-one/castelnuovo-rationality-criterion.md` |
| Separable descent of invariants | `surfaces/numerical-classification/kappa-minus-one/separable-generically-finite-invariant-descent.md` |
| Separable surface Lüroth | `surfaces/numerical-classification/kappa-minus-one/separable-surface-luroth.md` |
| Inseparable failure | `surfaces/numerical-classification/kappa-minus-one/inseparable-surface-luroth-failure.md` |
| Surface-type definition interface | `surfaces/numerical-classification/kappa-zero/surface-type-definition-api.md` |
| `kappa=0` and `12K` | `surfaces/numerical-classification/kappa-zero/kappa-zero-twelve-canonical-torsion.md` |
| K3 invariants | `surfaces/numerical-classification/kappa-zero/k3-surface-numerical-invariants.md` |
| Enriques invariants | `surfaces/numerical-classification/kappa-zero/enriques-surface-numerical-data.md` |
| Abelian and hyperelliptic data | `surfaces/numerical-classification/kappa-zero/abelian-hyperelliptic-surface-data.md` |
| Exhaustive `kappa=0` classification | `surfaces/numerical-classification/kappa-zero/kappa-zero-surface-classification.md` |
| Elliptic-surface fibration interface | `surfaces/numerical-classification/kappa-one/elliptic-surface-fibration.md` |
| Theorem 6.4 | `surfaces/numerical-classification/kappa-one/kappa-one-elliptic-surface-classification.md` |
| General-type definition | `surfaces/numerical-classification/general-type/surface-general-type-definition.md` |
| Theorem 6.5 | `surfaces/numerical-classification/general-type/kappa-two-pluricanonical-birationality.md` |
