---
article_id: af_430a8af54e5b37e77bb4ac7d
---

# Remaining-book roadmap

This records the completed source and dependency-DAG pass over the approved
remaining-book scope.
The 163 leaves through Corollary I.6.12 are formalized, and §I.7 has a 50-leaf
[fine roadmap](../intersections-projective-space/README.md), with 47 leaves
formalized and three remaining. Section I.8 has been dispositioned claim by
claim. Chapter II now has a 444-leaf
[fine roadmap](../schemes/README.md), with 99 exact pinned-Mathlib leaves and
345 project targets. All of Chapter III has a 288-leaf
[fine roadmap](../cohomology/README.md), with 19 exact Mathlib leaves and 269
project targets. All of Chapter IV has a 201-leaf [fine roadmap](../curves/README.md),
with two exact Mathlib leaves and 199 project targets, plus five reactivated
earlier-exercise prerequisites. All of Chapter V has a 230-leaf
[fine roadmap](../surfaces/README.md), with one exact Mathlib leaf and 229 project
targets, plus two reactivated III.7 prerequisites, one II.8 prerequisite,
two I.5 prerequisites, and one Appendix A HRR prerequisite. Appendix A has a
72-leaf [fine roadmap](../intersection-theory/README.md), all project targets.
Appendix B has a 69-leaf [fine roadmap](../transcendental-methods/README.md),
all project targets. Appendix C has a 69-leaf
[fine roadmap](../weil-conjectures/README.md), with one exact pinned-Mathlib
foundation and 68 project targets.

The intended full-pass policy is to cover the running mathematical text, adopt
exercises only when later included text depends on them, inventory expository
material explicitly, and attach a proof-level source whenever Hartshorne states
a deep result without proof. Exact locators are in the
[source inventory](../../sources/hartshorne.md).

## Chapter I completion

| Milestone | Source | Goal | Primary prerequisites or decisions |
| --- | --- | --- | --- |
| I-5C | §I.5 after Thm. 5.3, pp. 33–35 | Completions, Cohen structure, and analytic local type | Partial: regularity under completion and the analytic-isomorphism definition are decomposed for later uses; the remaining completion, Cohen, and analytic examples are `DEFERRED` |
| I-7A | §I.7 through Thm. 7.2, pp. 47–49 | Affine and projective intersection-dimension theorems | Exercises 2.10 and 3.15; current Chapter I dimension theory |
| I-7B | §I.7, Props. 7.3–7.6, pp. 49–52 | Numerical polynomials, graded prime filtrations, Hilbert–Serre, and degree | I-7A; choose an integer-indexed twist representation |
| I-7C | §I.7, Thm. 7.7 and Cor. 7.8, pp. 53–54 | Intersection multiplicity and Bézout | I-7B and Exercise 2.8 |
| I-7D | Exercise I.7.4, with Exercises I.7.3 and I.5.4 | Optional generic-line interpretation of degree | `OUT`: Exercise I.7.4 has no later consumer; I.7.3 and I.5.4 are independently adopted for IV.2.3 |
| I-8 | §I.8, pp. 55–59 | Survey claims dispositioned as Chapter I recaps, later previews, standalone source obligations, or exposition | Complete; the three standalone claims remain source-blocked rather than becoming underspecified nodes |

### Section I.8 disposition

The Chapter I survey has now been read claim by claim. Its birational,
projective-model, dimension, affine-cover, and coordinate-ring claims point to
existing Chapter I articles. Its substantive previews are assigned to the
specific Chapter II–V or Appendix A milestones that develop them. Editorial,
historical, and motivational passages are out of formalization scope.

Three assertions are neither recaps nor sufficiently specified later targets:
the existence and dimension of the moduli varieties `M_g`, a counterexample
showing that degree and Hilbert polynomial depend on projective embedding, and
a Noetherian affine scheme of infinite dimension. They remain deferred source
obligations until a precise modern statement and proof source are adopted; the
survey sentence alone is not used as a proof specification.

## Chapter II: schemes

| Milestone | Source | Goal | Primary prerequisites |
| --- | --- | --- | --- |
| II-A | §§II.1–3, pp. 60–95 | [Fine roadmap](../schemes/README.md): sheaves, `Spec`, `Proj`, schemes, morphisms, subschemes, products, and first properties | Complete source/API pass: 70 exact Mathlib leaves and 67 project targets |
| II-B | §II.4, pp. 95–108 | [Fine roadmap](../schemes/README.md): separated, proper, and projective morphisms and valuative criteria | Complete source/API pass: 11 exact Mathlib leaves and 24 project targets |
| II-C | §II.5, pp. 109–129 | [Fine roadmap](../schemes/README.md): quasi-coherent and coherent modules, projective sheaf machinery, relative Spec, and vector bundles | Complete source/API pass: 9 exact Mathlib leaves and 61 project targets |
| II-D | §§II.6–7, pp. 129–172 | [Fine roadmap](../schemes/README.md): divisors, Picard groups, K-theory, ampleness, relative Proj, projective bundles, and blowups | Complete source/API pass: 88 project targets and explicit external-source obligations |
| II-E | §II.8, pp. 172–190 | [Fine roadmap](../schemes/differentials/README.md): differentials, nonsingularity, Bertini, canonical sheaves, Cohen–Macaulay and lci geometry | Complete source/API pass: 5 exact Mathlib leaves, 69 project targets, and 5 explicit source-blocked nodes |
| II-F | §II.9, pp. 190–200 | [Fine roadmap](../schemes/formal-schemes/README.md): inverse systems, adic completions, formal neighborhoods, and coherent formal modules | Complete source/API pass: 4 exact Mathlib leaves, 36 project targets, and one source-blocked node |

## Chapter III: cohomology

| Milestone | Source | Goal | Primary prerequisites |
| --- | --- | --- | --- |
| III-A | §§III.1–4, pp. 202–225 | [Fine roadmap](../cohomology/README.md): derived functors, sheaf and supported cohomology, affine/local vanishing, and Čech comparison | Complete source/API pass: 5 exact Mathlib leaves, 67 project targets, and 12 explicit source-blocked nodes |
| III-B | §III.5, pp. 225–233 | [Fine roadmap](../cohomology/README.md): projective-space cohomology, Serre finiteness/vanishing, ampleness, and Hilbert polynomials | Complete source/API pass: 34 project targets and 7 explicit source-blocked roots |
| III-C | §§III.6–7, pp. 233–250 | [Fine roadmap](../cohomology/README.md): global and sheaf Ext, dualizing sheaves, Serre duality, residues, and Kodaira's theorem | Complete source/API pass: 5 exact Mathlib leaves, 62 project targets, and 9 explicit source-blocked nodes |
| III-D | §§III.8–9, pp. 250–268 | [Fine roadmap](../cohomology/README.md): higher direct images, flatness, base change, Hilbert polynomials, families, and deformations | Complete source/API pass: 9 exact Mathlib leaves, 48 project targets, and 9 explicit source-blocked roots |
| III-E | §III.10, pp. 268–276 | [Fine roadmap](../cohomology/README.md): smooth morphisms, generic smoothness, homogeneous spaces, Kleiman transversality, and Bertini | Complete source/API pass: 29 project targets and one source-blocked PGL-action root |
| III-F | §§III.11–12, pp. 276–292 | [Fine roadmap](../cohomology/README.md): formal functions, Zariski's Main Theorem, Stein factorization, semicontinuity, Grauert, and base change | Complete source/API pass: 29 project targets and one higher-direct-image representation blocker |

## Chapter IV: curves

| Milestone | Source | Goal | Primary prerequisites |
| --- | --- | --- | --- |
| IV-A | §§IV.1–2, pp. 294–306 | [Fine roadmap](../curves/README.md): Riemann–Roch, morphisms of curves, ramification, Frobenius, and Hurwitz | Complete source/API pass: 46 project targets, one exact Mathlib target, three reactivated prerequisites, and one source-blocked node |
| IV-B | §IV.3, pp. 307–316 | [Fine roadmap](../curves/projective-embeddings/README.md): linear systems, projections, strange curves, nodal plane models, and Severi loci | Complete source/API pass: 30 project targets, two reactivated prerequisites, and one Harris source blocker |
| IV-C | §IV.4, pp. 316–340 | [Fine roadmap](../curves/elliptic-curves/README.md): elliptic curves, group laws, Jacobians, uniformization, complex multiplication, Hasse invariants, and rational points | Complete source/API pass: 74 project targets, one exact Mathlib target, and nine explicit source/representation blockers |
| IV-D | §§IV.5–6, pp. 340–355 | [Fine roadmap](../curves/README.md): canonical curves, Clifford's theorem, curve moduli, Castelnuovo's bound, and space-curve classifications | Complete source/API pass: 49 project targets and six explicit source blockers |

## Chapter V: surfaces

| Milestone | Source | Goal | Primary prerequisites |
| --- | --- | --- | --- |
| V-A | §V.1, pp. 357–368 | [Fine roadmap](../surfaces/README.md): surface intersection theory, adjunction, Riemann–Roch, Hodge index, and Nakai | Complete source/API pass: 42 project targets, one exact Mathlib target, two reactivated III.7 prerequisites, one Appendix A HRR blocker, and two section source blockers |
| V-B | §V.2, pp. 369–385 | [Fine roadmap](../surfaces/ruled-surfaces/README.md): ruled surfaces, normalized bundles, scrolls, and ample cones | Complete source/API pass: 48 project targets, one reactivated II.8 prerequisite, two explicit source blockers, and an inherited projective-bundle blocker |
| V-C | §V.3, pp. 386–395 | [Fine roadmap](../surfaces/monoidal-transformations/README.md): point blowups, exceptional curves, strict transforms, and embedded curve resolution | Complete source/API pass: 32 project targets and one reactivated I.5 analytic-classification blocker |
| V-D | §V.4, pp. 395–409 | [Fine roadmap](../surfaces/cubic-surfaces/README.md): assigned systems, Del Pezzo blowups, the 27 lines, and ample cones | Complete source/API pass: 42 project targets and four explicit source blockers |
| V-E | §V.5, pp. 409–420 | [Fine roadmap](../surfaces/birational-transformations/README.md): birational factorization, contraction, and minimal models | Complete source/API pass: 39 project targets, one reactivated I.5 completion blocker, and three explicit section blockers |
| V-F | §V.6, pp. 421–423 | [Fine roadmap](../surfaces/numerical-classification/README.md): canonical rings, Kodaira dimension, and numerical classification | Complete claim-by-claim source/API pass: 26 project targets and thirteen explicit source blockers |

## Appendices

| Milestone | Source | Goal | Primary prerequisites or source obligations |
| --- | --- | --- | --- |
| A-A | Appendix A §§1–2, pp. 424–429 | [Fine roadmap](../intersection-theory/README.md): cycles, rational equivalence, Chow groups, and intersection products | Complete source/API pass: 29 section targets plus Exercises 6.2–6.3 and explicit outline-source blockers |
| A-B | Appendix A §3, pp. 429–431 | [Fine roadmap](../intersection-theory/chern-classes/README.md): Chern classes, zero loci, and self-intersection | Complete source/API pass: 15 section targets plus Exercise 6.6 and four explicit source blockers |
| A-C | Appendix A §§4–5, pp. 431–437 | [Fine roadmap](../intersection-theory/README.md): HRR, positivity, Hodge index, K-theory, GRR, and generalizations | Complete source/API pass: 25 project targets and ten explicit source blockers |
| B-A | Appendix B §§1–2, pp. 438–441 | [Fine roadmap](../transcendental-methods/README.md): analytic spaces, analytification, comparison, GAGA, and Chow | Complete source/API pass: 27 section targets plus Exercise 6.6 and twenty explicit blockers |
| B-B | Appendix B §§3–4, pp. 441–446 | [Fine roadmap](../transcendental-methods/README.md): algebraicity, Moishezon, Kähler, and Hodge criteria | Complete source/API pass: 21 project targets and eleven explicit blockers |
| B-C | Appendix B §5, pp. 446–448 | [Fine roadmap](../transcendental-methods/README.md): exponential sequence, Picard/NS, and Jacobian lattices | Complete source/API pass: 20 project targets and seven explicit blockers |
| C-A | Appendix C §1, pp. 449–451 | [Fine roadmap](../weil-conjectures/README.md): zeta functions and the Weil theorem package | Complete source/API pass: 20 project targets inheriting the explicit §§3–4 source blockers |
| C-B | Appendix C §3, pp. 453–454 | [Fine roadmap](../weil-conjectures/etale-cohomology/README.md): the étale–ℓ-adic cohomology interface | Complete source/API pass: one exact Mathlib target, 28 project targets, and eleven explicit blockers |
| C-C | Appendix C §4, pp. 454–457 | [Fine roadmap](../weil-conjectures/deductions/README.md): Frobenius, trace formulas, rationality, functional equation, and Deligne's theorem | Complete source/API pass: 20 project targets and five explicit blockers |

Appendix C §2 is historical exposition and Exercises C.5.1–5.7 have no later
consumer. Appendix A Exercise 6.6 is adopted for Appendix C's diagonal/top-
Chern identity; Appendix B Exercise 6.6 is adopted for the comparison assertion
left to the reader in Appendix B §2.

## Dependency spine and approval boundary

The main spine is `II-A → II-C → III-A → III-B/III-C/III-D`, with II-B,
II-D, II-E, and II-F branching into the later cohomology, curve, and surface
milestones. Chapter IV builds on Chapters II–III; Chapter V builds on II–IV;
the appendices consolidate those chapters and add substantial external source
obligations. The I.7 algebraic branch can proceed independently from most of
the scheme-theoretic spine.

The fine pass has reached the end of Appendix C. Future roadmap changes should
preserve dependency order and the approved exercise policy: optional exercise
chains are not silently adopted, and an unsourced deep theorem is not turned
into a proof specification.
