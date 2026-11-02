# Hartshorne, Algebraic Geometry

A mathematical guide to Robin Hartshorne's *Algebraic Geometry*, with linked
statements and Lean 4 formalization progress across classical varieties,
schemes, cohomology, curves, surfaces, and the three appendices.

## Start reading

- [Book roadmap](roadmap/README.md): chapter introductions, definitions,
  theorems, and the dependencies between them.
- [Source coverage](coverage/README.md): adopted material, exercise policy,
  exclusions, and deferred source obligations.
- [Source notes](sources/README.md): exact book locators and supporting
  references, available in the repository.
- [Milestone ledger](roadmap/remaining-book/README.md): the source and
  prerequisite structure of the later chapters and appendices.

The book begins with the classical language of affine and projective
varieties. Schemes and sheaves then provide the setting for cohomology and
the geometry of curves and surfaces. Each chapter overview introduces its
mathematical role before leading to individual statement cards.

## Follow a statement

A statement card gives the intended mathematics, its current formalization
status, and its sources. **Depends on** lists what is needed to state it;
**Proof depends on** lists additional results needed for its proof. Where a
Lean declaration is recorded, the source link opens the corresponding code.

The dependency map offers another way through the material: select a topic,
open its chapter, then inspect a statement and its immediate prerequisites.
The book and the map describe the same Markdown roadmap.

## Understand the progress

Progress summaries are generated from the current declarations and dependency
links. A fully proved target is complete together with its prerequisites;
conditional proofs are labelled separately and name their open assumptions.
The summary's percentage counts formalizable leaf targets, not pages or the
whole source text.

Source coverage answers a different question. A decomposed area has explicit
roadmap statements, which may still await formalization. Read the
[coverage contract](coverage/README.md) for the adopted boundary and the
remaining source obligations.

## About the formalization

The Lean development builds on Mathlib while supplying the classical-variety
constructions used in Chapter I. Completed milestones include the affine
variety and coordinate-ring correspondence, normalization and projective
models of nonsingular curves, and the intersection-theory development of
Section I.7. Later formalized results appear alongside the planned material
in their own chapter pages.

For bibliographic details, exact locators, and the distinction between
Hartshorne's statements and adopted supporting results, consult the
[source notes](sources/README.md).
