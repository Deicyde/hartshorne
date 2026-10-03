# Hartshorne Appendix B §5, the exponential sequence

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Appendix B, §5. The section occupies printed pp.446–447. Exercises 6.1–6.4
begin on p.447 and Exercises 6.5–6.6 finish on p.448. Appendix C begins on
p.449; there is no continuation.

The section applies the analytic exponential sequence to projective complex
varieties, uses GAGA to return to algebraic Picard groups, and identifies the
Picard torus of a curve with its Jacobian.

## The exponential sequence, printed p.446

Normalize the exponential map as

`z |-> exp(2*pi*i*z)`.

It gives an exact sequence of abelian groups

`0 -> Z -> C -> C^* -> 0`.

On a reduced complex analytic space, local holomorphic logarithms sheafify
this to an exact sequence on the analytic topology

`0 -> Z -> O -> O^* -> 0`.

For a connected reduced projective complex variety, global holomorphic
functions are constant and `C -> C^*` is surjective. The associated long
exact sequence therefore begins

`0 -> H^1(X^h,Z) -> H^1(X^h,O) -> H^1(X^h,O^*)`

`-> H^2(X^h,Z) -> H^2(X^h,O) -> ...`.

The constant integer sheaf and all cohomology in this display live on the
analytic topology, not the Zariski site.

Projective GAGA identifies coherent analytic and algebraic cohomology of the
structure sheaf and gives `Pic(X^h)~=Pic(X)`. Thus the sequence becomes

`0 -> H^1(X^h,Z) -> H^1(X,O_X) -> Pic(X)`

`-> H^2(X^h,Z) -> H^2(X,O_X) -> ...`.

## Picard and NeronSeveri, printed p.447

The exponential boundary gives the topological first Chern class

`c_1^top:Pic(X)->H^2(X^h,Z)`.

Hartshorne says that algebraically equivalent Cartier divisors have the same
topological class. Consequently `NS(X)` embeds in `H^2(X^h,Z)`.

He cites triangulability of algebraic varieties to conclude that integral
cohomology is finitely generated, and hence that `NS(X)` is finitely
generated. Both the triangulation theorem and the algebraic-equivalence
comparison need explicit proof sources.

Exactness also identifies

`Pic^0(X) ~= H^1(X,O_X)/image(H^1(X^h,Z))`.

The image is a lattice, making the quotient a compact complex torus.
Hartshorne then states that this torus is algebraic: it is the Picard variety
of `X`. The analytic-torus and algebraicity assertions are kept as distinct
claims.

## The curve and its Jacobian, printed p.447

For a smooth projective complex genus-`g` curve, the analytification is a
compact oriented real surface homeomorphic to a sphere with `g` handles.
Therefore

`H^0(C^h,Z)=Z`, `H^1(C^h,Z)=Z^(2g)`, `H^2(C^h,Z)=Z`.

Algebraic coherent cohomology and GAGA give `H^1(C,O_C)~=C^g`. The
exponential-sequence lattice then yields

`Pic^0(C) ~= C^g/Z^(2g)`.

Hartshorne identifies this algebraic abelian variety with the Jacobian and
records `NS(C)~=Z` via the degree map. A proof-level analytic/algebraic
Jacobian comparison is still required.

## Exercise disposition, printed pp.447–448

- **Exercises 6.1–6.5 — OUT.** The disc, nonalgebraic analytic sheaf,
  nonalgebraic analytic line bundle, properness/global-section comparison, and
  affine-curve analytification rigidity are not used by later included running
  text.
- **Exercise 6.6 — ADOPTED.** It proves the projective-scheme morphism part of
  GAGA: every analytic morphism `X^h -> Y^h` between projective complex
  schemes is the analytification of a unique algebraic morphism. The source
  inventory already records this comparison as a clause left to the reader by
  §2.

No Appendix C running text cites another Appendix-B exercise.

## External proof sources and blockers

- Serre, GAGA, supplies coherent-category, cohomology, and Picard comparison.
  These are inherited Appendix B §§1–2 source obligations.
- Gunning–Rossi, or an equivalent analytic-sheaf source, supplies local
  holomorphic logarithms and analytic sheaf cohomology.
- Hironaka's triangulation theorem supplies finite generation of integral
  cohomology.
- Algebraic equivalence preserving the topological Chern class needs a
  family/homotopy or Picard-functor proof.
- The Picard torus's algebraicity needs an exact Chow/Grothendieck Picard-
  variety source.
- Compact-Riemann-surface topology and the algebraic-genus/topological-genus
  comparison need a precise source.
- The analytic period torus's identification with the algebraic Jacobian
  needs an exact comparison theorem.

The roadmap isolates seven new explicit blocker roots in §5: triangulation,
algebraic-equivalence invariance, the Picard lattice/complex-torus theorem,
the comparison of that torus with algebraic `Pic^0`, Picard-variety
algebraicity, Riemann-surface topology, and analytic/algebraic Jacobian
comparison. Other blocked status is inherited from the earlier GAGA
branch.

## Pinned Mathlib audit and false friends

The pinned checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). No §5 leaf is an
exact pinned-Mathlib result.

Mathlib contains the complex exponential and portions of singular homology
and topology, but no complex analytic spaces, analytic structure sheaf,
analytic sheaf cohomology, analytification, GAGA, exponential sequence of
sheaves, triangulation of varieties, topological Chern class from Picard
groups, Picard torus/variety, or compact-Riemann-surface period lattice.

`CommRing.Pic` is the Picard group of a ring, not an analytic or scheme
Picard group. Topological/manifold vector bundles and the algebraic elliptic-
curve/Jacobian APIs do not supply the analytic period comparison.

## Representation choices and warnings

- Keep analytic and Zariski sites, sheaves, and cohomology objects distinct;
  use GAGA comparison morphisms explicitly.
- Normalize exponential by `2*pi*i`, so its kernel is literally `Z`.
- Construct `Pic` through `H^1(O^*)`, not the Picard group of a ring.
- Prove the image of `H^1(X^h,Z)` is a discrete cocompact lattice before
  forming the complex torus quotient.
- Separate “complex torus” from “abelian variety/Picard variety.”
- On curves, identify the actual period lattice; do not read `Z^(2g)` as a
  canonical coordinate lattice without choices.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Complex exponential exact sequence | `transcendental-methods/exponential-picard/exponential/complex-exponential-exact-sequence.md` |
| Analytic exponential sheaf sequence | `transcendental-methods/exponential-picard/exponential/analytic-exponential-sheaf-sequence.md` |
| Proper reduced global holomorphic functions | `transcendental-methods/exponential-picard/exponential/proper-reduced-holomorphic-functions-constant.md` |
| Exponential long exact sequence | `transcendental-methods/exponential-picard/exponential/exponential-long-exact-sequence.md` |
| Structure-sheaf GAGA cohomology | `transcendental-methods/exponential-picard/exponential/gaga-structure-sheaf-cohomology.md` |
| Picard GAGA comparison | `transcendental-methods/exponential-picard/exponential/gaga-picard-comparison.md` |
| Topological first Chern class | `transcendental-methods/exponential-picard/picard/topological-first-chern-class.md` |
| Algebraic equivalence preserves class | `transcendental-methods/exponential-picard/picard/algebraic-equivalence-topological-class.md` |
| Triangulation and finite cohomology | `transcendental-methods/exponential-picard/picard/triangulation-integral-cohomology-finite.md` |
| Néron–Severi injection | `transcendental-methods/exponential-picard/picard/neron-severi-injective-integral-cohomology.md` |
| Complex Néron–Severi finite generation | `transcendental-methods/exponential-picard/picard/neron-severi-finite-generation-complex.md` |
| Pic0 quotient | `transcendental-methods/exponential-picard/picard/pic-zero-cohomology-quotient.md` |
| Pic0 complex torus | `transcendental-methods/exponential-picard/picard/pic-zero-complex-torus.md` |
| Picard variety algebraicity | `transcendental-methods/exponential-picard/picard/picard-variety-algebraicity.md` |
| Compact Riemann-surface topology | `transcendental-methods/exponential-picard/curves/compact-riemann-surface-topology.md` |
| Integral cohomology of the curve | `transcendental-methods/exponential-picard/curves/compact-riemann-surface-integral-cohomology.md` |
| Curve structure-sheaf cohomology | `transcendental-methods/exponential-picard/curves/curve-structure-sheaf-h1.md` |
| Jacobian period lattice | `transcendental-methods/exponential-picard/curves/curve-jacobian-period-lattice.md` |
| Analytic Pic0 of a curve | `transcendental-methods/exponential-picard/curves/curve-pic-zero-analytic-torus.md` |
| Algebraic Jacobian comparison | `transcendental-methods/exponential-picard/curves/curve-jacobian-algebraic-comparison.md` |

## Adopted-exercise map

| Source result | Roadmap article |
|---|---|
| Exercise 6.6 | `transcendental-methods/gaga/exercises/projective-analytic-morphism-algebraization.md` |
