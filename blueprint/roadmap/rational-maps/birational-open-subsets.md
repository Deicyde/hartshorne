---
article_id: af_66e36fc9e3926617642cdd2d
declaration: theorem
origin: cited
source_units: [chapter-i-section-4]
statement: formalized
proof: formalized
lean: Hartshorne.birational_iff_hasIsomorphicOpenSubsets
---

# Birational varieties have isomorphic open subsets

For separated varieties `X` and `Y`, the following are equivalent:

- `X` and `Y` are birationally equivalent;
- there are nonempty open subsets `U ⊆ X` and `V ⊆ Y` such that the
  restricted varieties on `U` and `V` are isomorphic.

For the forward implication, choose representatives of mutually inverse
rational maps.  Restrict their domains once more so that each map lands in the
domain of the other.  The rational inverse equations then hold everywhere on
those smaller opens and give inverse morphisms.  Conversely, an isomorphism of
nonempty opens and its inverse define dominant rational maps because every
nonempty open subset of an irreducible variety is dense.

This is the geometric `(i) ⇔ (ii)` part of Corollary 4.5.

## Depends on

- [Birational maps](birational-map.md)
- [Composition of dominant rational maps](rational-map-composition.md)

## Proof depends on

- [Morphisms agreeing on an open set](morphism-agreement.md)
- [Rational maps and function fields](rational-map-function-field.md)

## Sources

- [Hartshorne I.4, Corollary 4.5 (p. 26)](../../sources/hartshorne.md#i4)
