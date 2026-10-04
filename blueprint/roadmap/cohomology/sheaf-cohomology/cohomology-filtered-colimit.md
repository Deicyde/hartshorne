---
article_id: af_42ed22e1dd5ef7e9629f6a0c
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-1-4]
---

# Cohomology commutes with filtered colimits

If `X` is noetherian and `(F_a)` is a filtered diagram of abelian sheaves,
then the canonical maps

`colim_a Hⁿ(X,F_a) ⟶ Hⁿ(X,colim_a F_a)`

are natural isomorphisms for all `n`. Consequently sheaf cohomology on `X`
commutes with arbitrary direct sums.

The proof compares two effaceable delta functors using functorial embeddings
into discontinuous-section sheaves and preservation of flasqueness.

## Depends on

- [Sheaf cohomology and the Ext model](sheaf-cohomology.md)

## Proof depends on

- [Filtered colimits preserve flasqueness](filtered-colimit-flasque.md)
- [Universality characterizes derived functors](../derived-functors/derived-functor-universality.md)
- [The Godement flasque embedding](godement-discontinuous-sections.md)
- [Flasque sheaves are acyclic](flasque-sheaf-acyclic.md)

## Sources

- [Hartshorne III.2, Proposition 2.9 and Remark 2.9.1, printed p. 209](../../../sources/hartshorne-iii-1-2.md#filtered-colimits-and-closed-support-printed-pp-208210)
