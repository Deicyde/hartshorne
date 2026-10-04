---
article_id: af_0a1032d4064bbb5485d0d291
declaration: definition
origin: cited
source_units: [chapter-ii-section-5]
---

# Locally free and invertible module sheaves

Define free and locally free `𝒪_X`-modules, locally free modules of a specified
finite rank, and invertible modules as the rank-one case.  Show that the rank
of a locally free module is locally constant, hence constant when `X` is
connected.

Pinned Mathlib provides `SheafOfModules.IsLocallyFree`, but does not yet expose
the fixed-rank and invertible-sheaf API required by Hartshorne, so the full
source statement remains a project leaf.

## Depends on

- [Sheaves of modules](sheaves-of-modules.md)

## Proof depends on

- Invariant basis number for nonzero local rings.
- Locality of isomorphisms of sheaves of modules.

## Sources

- [Hartshorne II.5, free, locally free, and invertible sheaves on printed p. 109](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
