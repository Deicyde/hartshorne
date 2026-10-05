---
article_id: af_09426dc441c92bf1aaec50d6
declaration: def
origin: cited
source_units: [appendix-a-sections-1-2]
statement: formalized
lean: Hartshorne.codimensionCycles
---

# Codimension cycles on a variety

For a variety `X` and `r>=0`, define `Z^r(X)` to be the free abelian group on
the irreducible closed subvarieties of codimension `r`. Thus a cycle is a
finite sum `sum_i n_i[Y_i]` with `n_i` integral.

This is the codimension grading used throughout Appendix A. It is a
finite-support specialization of Mathlib's locally finite generic-point
cycles, not a second ungraded cycle representation.

The Lean definition makes the same construction for an arbitrary scheme,
harmlessly generalizing the source's variety hypothesis.

Roadmap note: the irreducible-components dependency is retained as context for
the source's finite-sum presentation. The Lean declaration does not consume it
because Mathlib's algebraic cycles are already indexed by generic points of
irreducible closed subsets.

## Depends on

- [Codimension in a scheme](../../../schemes/subschemes-and-dimension/scheme-codimension.md)
- [Irreducible components](../../../affine-varieties/irreducible-decomposition.md)

## Sources

- [Hartshorne Appendix A.1, cycle definition, p.425](../../../../sources/hartshorne-appendix-a-1-2.md)
