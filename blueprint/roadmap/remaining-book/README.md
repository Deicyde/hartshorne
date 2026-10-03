---
article_id: af_430a8af54e5b37e77bb4ac7d
---

# Remaining-book roadmap

This is the approved coarse plan for a full pass over the rest of Hartshorne.
The 163 leaves through Corollary I.6.12 are formalized, and §I.7 has a 50-leaf
[fine roadmap](../intersections-projective-space/README.md), with 47 leaves
formalized and three remaining. Section I.8 has been dispositioned claim by
claim. Chapter II now has a 443-leaf
[fine roadmap](../schemes/README.md), with 99 exact pinned-Mathlib leaves and
344 project targets. All of Chapter III has a 288-leaf
[fine roadmap](../cohomology/README.md), with 19 exact Mathlib leaves and 269
project targets. All of Chapter IV has a 201-leaf [fine roadmap](../curves/README.md),
with two exact Mathlib leaves and 199 project targets, plus five reactivated
earlier-exercise prerequisites and one forward V.2 prerequisite. Chapter V §1
has a 43-leaf [fine roadmap](../surfaces/README.md), with one exact Mathlib leaf
and 42 project targets, plus two reactivated III.7 prerequisites and one forward
Appendix A prerequisite. Chapter V §§2–6 and Appendices A–C remain
explicit deferred milestones in the [coverage contract](../../coverage/README.md)
until their turn for fine source and Mathlib work.

The intended full-pass policy is to cover the running mathematical text, adopt
exercises only when later included text depends on them, inventory expository
material explicitly, and attach a proof-level source whenever Hartshorne states
a deep result without proof. Exact locators are in the
[source inventory](../../sources/hartshorne.md).

## Chapter I completion

| Milestone | Source | Goal | Primary prerequisites or decisions |
| --- | --- | --- | --- |
| I-5C | §I.5 after Thm. 5.3, pp. 33–35 | Completions, Cohen structure, and analytic local type | Already `DEFERRED`; choose a proof source before decomposition |
| I-7A | §I.7 through Thm. 7.2, pp. 47–49 | Affine and projective intersection-dimension theorems | Exercises 2.10 and 3.15; current Chapter I dimension theory |
| I-7B | §I.7, Props. 7.3–7.6, pp. 49–52 | Numerical polynomials, graded prime filtrations, Hilbert–Serre, and degree | I-7A; choose an integer-indexed twist representation |
| I-7C | §I.7, Thm. 7.7 and Cor. 7.8, pp. 53–54 | Intersection multiplicity and Bézout | I-7B and Exercise 2.8 |
| I-7D | Exercise I.7.4, with Exercises I.7.3 and I.5.4 | Optional generic-line interpretation of degree | Decide whether to adopt this exercise chain |
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
| II-C | §II.5, pp. 109–129 | [Fine roadmap](../schemes/README.md): quasi-coherent and coherent modules, projective sheaf machinery, relative Spec, and vector bundles | Complete source/API pass: 9 exact Mathlib leaves and 60 project targets |
| II-D | §§II.6–7, pp. 129–172 | [Fine roadmap](../schemes/README.md): divisors, Picard groups, K-theory, ampleness, relative Proj, projective bundles, and blowups | Complete source/API pass: 88 project targets and explicit external-source obligations |
| II-E | §II.8, pp. 172–190 | [Fine roadmap](../schemes/differentials/README.md): differentials, nonsingularity, Bertini, canonical sheaves, Cohen–Macaulay and lci geometry | Complete source/API pass: 5 exact Mathlib leaves, 68 project targets, and 5 explicit source-blocked nodes |
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
| IV-D | §§IV.5–6, pp. 340–355 | [Fine roadmap](../curves/README.md): canonical curves, Clifford's theorem, curve moduli, Castelnuovo's bound, and space-curve classifications | Complete source/API pass: 49 project targets, six explicit section blockers, and one forward V.2 blocker |

## Chapter V: surfaces

| Milestone | Source | Goal | Primary prerequisites |
| --- | --- | --- | --- |
| V-A | §V.1, pp. 357–368 | [Fine roadmap](../surfaces/README.md): surface intersection theory, adjunction, Riemann–Roch, Hodge index, and Nakai | Complete source/API pass: 42 project targets, one exact Mathlib target, two reactivated III.7 prerequisites, one forward Appendix A blocker, and two section source blockers |
| V-B | §V.2, pp. 369–385 | Ruled surfaces | V-A and IV curve theory |
| V-C | §V.3, pp. 386–394 | Blowups and resolution steps | II-F, III-F, and V-A |
| V-D | §V.4, pp. 395–408 | Cubic surfaces and the 27 lines | V-A and V-C |
| V-E | §V.5, pp. 409–420 | Birational factorization, contraction, and minimal models | V-B through V-D |
| V-F | §V.6, pp. 421–423 | Classification survey | Split proved claims from survey assertions and source each retained claim |

## Appendices

| Milestone | Source | Goal | Primary prerequisites or source obligations |
| --- | --- | --- | --- |
| A-A | Appendix A §§1–2, pp. 424–429 | Chow groups and intersection products | II-D; Hartshorne gives an outline, so adopt cited proof sources |
| A-B | Appendix A §3, pp. 429–431 | Chern classes and self-intersection | A-A and II-E |
| A-C | Appendix A §§4–5, pp. 431–437 | Hirzebruch–Riemann–Roch, positivity, Hodge index, and Grothendieck–Riemann–Roch | A-B, III, IV-A, and V-A; adopt external sources |
| B-A | Appendix B §§1–2, pp. 438–441 | Analytification, GAGA, and Chow's theorem | II and III-B; adopt analytic/GAGA sources |
| B-B | Appendix B §§3–4, pp. 441–446 | Algebraicity and Kähler criteria | B-A, IV, and V; adopt analytic/Hodge sources |
| B-C | Appendix B §5, pp. 446–448 | Exponential sequence and Picard theory | B-A, III, and IV-C |
| C-A | Appendix C §1, pp. 449–451 | Zeta functions and the Weil assertions | Finite-field scheme geometry |
| C-B | Appendix C §3, pp. 453–454 | The ℓ-adic cohomology interface | II and III plus an external étale-cohomology source stack |
| C-C | Appendix C §4, pp. 454–458 | Frobenius, trace formulas, rationality, functional equation, and Deligne's theorem | C-A, C-B, Appendix A, Appendix B, and IV-A; adopt proof-level sources |

Appendix C §2 is historical exposition. Appendix A Exercise 6.6 and Appendix B
Exercise 6.6 are prospective exceptions to the exercise policy because later
appendix text uses them.

## Dependency spine and approval boundary

The main spine is `II-A → II-C → III-A → III-B/III-C/III-D`, with II-B,
II-D, II-E, and II-F branching into the later cohomology, curve, and surface
milestones. Chapter IV builds on Chapters II–III; Chapter V builds on II–IV;
the appendices consolidate those chapters and add substantial external source
obligations. The I.7 algebraic branch can proceed independently from most of
the scheme-theoretic spine.

The roadmap is authorized to continue through these milestones autonomously,
working in dependency order and pausing only for a genuinely unresolved source
or scope choice. The approved exercise policy does not silently adopt optional
exercise chains or turn an unsourced deep theorem into a proof specification.
