# Hartshorne, Algebraic Geometry

A Lean 4 and Mathlib formalization project with a mathematical wiki covering
Robin Hartshorne's *Algebraic Geometry* (Springer, Graduate Texts in Mathematics
52, 1977). The roadmap spans Chapters I–V and Appendices A–C.

**[Read the wiki](https://deicyde.github.io/hartshorne/)** ·
**[Explore the dependency map](https://deicyde.github.io/hartshorne/dependencies/map/index.html)** ·
**[Check the source coverage](blueprint/coverage/README.md)**

## About the project

The wiki presents the book as linked definitions, theorems, and proof
prerequisites. Each statement points to its source, and formalized statements
link to the corresponding Lean declarations. The dependency map shows how the
pieces fit together and which prerequisites remain to be completed.

The classical development in Chapter I includes affine and projective
varieties, regular functions, morphisms, dimension, normalization, nonsingular
curve models, and intersection theory. Later chapters build on Mathlib's
schemes and sheaves to develop cohomology, curves, and surfaces. The appendices
provide the intersection-theoretic, analytic, and étale-cohomological context.

Formalization is ongoing. The wiki's generated progress summaries give the
current state of each area; the [coverage contract](blueprint/coverage/README.md)
records the adopted material, exclusions, and deferred source obligations.

## Find your way around

| Area | Topics | Entry point |
| --- | --- | --- |
| Chapter I | Classical varieties, morphisms, dimension, and nonsingular curves | [Book roadmap](blueprint/roadmap/README.md) |
| Chapter II | Schemes, sheaves, modules, divisors, and projective geometry | [Schemes](blueprint/roadmap/schemes/README.md) |
| Chapter III | Cohomology, duality, families, and base change | [Cohomology](blueprint/roadmap/cohomology/README.md) |
| Chapter IV | Riemann–Roch, ramification, elliptic curves, and projective embeddings | [Curves](blueprint/roadmap/curves/README.md) |
| Chapter V | Intersection theory, birational geometry, and surface classification | [Surfaces](blueprint/roadmap/surfaces/README.md) |
| Appendix A | Chow groups, Chern classes, and Riemann–Roch | [Intersection theory](blueprint/roadmap/intersection-theory/README.md) |
| Appendix B | Analytification, GAGA, and transcendental methods | [Transcendental methods](blueprint/roadmap/transcendental-methods/README.md) |
| Appendix C | Zeta functions, étale cohomology, and the Weil conjectures | [Zeta functions](blueprint/roadmap/weil-conjectures/README.md) |

Start with a chapter overview, then follow a statement's dependencies to its
definitions and supporting results. Use the map to explore connections across
chapters, and the [source notes](blueprint/sources/README.md) for exact book
locators and adopted supporting references.

## Reading the progress summaries

The site derives progress from the roadmap's recorded Lean declarations and
dependency links. A planned statement has not yet been formalized; a fully
proved target is complete together with its prerequisites. Any conditional
proof is labelled separately and lists the open statements it assumes.

The fully proved percentage measures formalizable leaf targets. Source
coverage is recorded separately: decomposing an area into statements does not
mean all of those statements have been proved.

## Toolchain and project files

The project uses Lean 4 `v4.33.1` and Mathlib `v4.33.1`.

- [Blueprint vault](blueprint/README.md): the source of the wiki and roadmap.
- [Lean development](src/Hartshorne.lean): the library's main import file.
- [Source coverage](blueprint/coverage/README.md): the boundary of the project.

Developed with [AutoformBot](https://github.com/facebookresearch/autoform-bot).
