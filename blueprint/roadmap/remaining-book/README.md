# Remaining-book roadmap

This is the coarse plan for a full pass over the rest of Hartshorne. It is a
proposal for approval, not a fine theorem DAG and not a formalization
commitment. The accepted fine roadmap currently ends at Corollary I.6.12, and
all 163 of its leaves are formalized. The [coverage contract](../../coverage/README.md)
therefore marks the mathematical units below `MAPPED` until their scope and
source stack are approved.

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
| I-8 | §I.8, pp. 55–59 | Inventory and disposition of substantive unnumbered survey claims | Decide claim by claim whether later chapters subsume, defer, or require a node |

## Chapter II: schemes

| Milestone | Source | Goal | Primary prerequisites |
| --- | --- | --- | --- |
| II-A | §§II.1–3, pp. 60–94 | Sheaves, `Spec`, `Proj`, schemes, morphisms, subschemes, products, and first properties | Commutative algebra and topology; audit exact Mathlib scheme APIs |
| II-B | §II.4, pp. 95–107 | Separated and proper morphisms and valuative criteria | II-A |
| II-C | §II.5, pp. 108–128 | Quasi-coherent and coherent modules | II-A |
| II-D | §§II.6–7, pp. 129–171 | Divisors, Picard groups, linear systems, ampleness, projective bundles, and blowups | II-B and II-C |
| II-E | §II.8, pp. 172–189 | Differentials, regularity, canonical sheaves, and Bertini | II-B and II-C |
| II-F | §II.9, pp. 190–200 | Completions and formal schemes | II-A and II-C; later needed by III-F and V-C |

## Chapter III: cohomology

| Milestone | Source | Goal | Primary prerequisites |
| --- | --- | --- | --- |
| III-A | §§III.1–4, pp. 202–224 | Derived functors, sheaf cohomology, affine vanishing, and Čech cohomology | II-A and II-C; external source for quoted homological algebra |
| III-B | §III.5, pp. 225–232 | Projective-space cohomology and coherent finiteness | III-A and II-D |
| III-C | §§III.6–7, pp. 233–249 | Ext and Serre duality | III-A and III-B |
| III-D | §§III.8–9, pp. 250–267 | Higher direct images, flat families, and Hilbert polynomials | III-A, III-B, and II-C |
| III-E | §III.10, pp. 268–275 | Smooth morphisms, generic smoothness, and Bertini | II-E and III-A |
| III-F | §§III.11–12, pp. 276–292 | Formal functions, Zariski's Main Theorem, Stein factorization, semicontinuity, and base change | II-F and III-D |

## Chapter IV: curves

| Milestone | Source | Goal | Primary prerequisites |
| --- | --- | --- | --- |
| IV-A | §§IV.1–2, pp. 294–306 | Riemann–Roch, morphisms of curves, ramification, and Hurwitz | II-D, II-E, and III-C |
| IV-B | §IV.3, pp. 307–315 | Linear systems, projective embeddings, and nodal plane models | IV-A |
| IV-C | §IV.4, pp. 316–339 | Elliptic curves, group laws, isogenies, and classification | IV-A; source the analytic results 4.12B–4.15B |
| IV-D | §§IV.5–6, pp. 340–355 | Canonical curves, Clifford's theorem, and space curves | IV-A and IV-B |

## Chapter V: surfaces

| Milestone | Source | Goal | Primary prerequisites |
| --- | --- | --- | --- |
| V-A | §V.1, pp. 357–368 | Surface intersection theory, adjunction, Riemann–Roch, Hodge index, and Nakai | II-D and III-C |
| V-B | §V.2, pp. 369–385 | Ruled surfaces | V-A and IV curve theory |
| V-C | §V.3, pp. 386–394 | Blowups and resolution steps | II-F and V-A |
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

Approval of this page would authorize the roadmap to decompose the entire
approved `MAPPED` scope autonomously, working milestone by milestone and
pausing only for a genuinely unresolved source or scope choice. It would not
by itself approve every optional exercise or an unsourced deep theorem.
