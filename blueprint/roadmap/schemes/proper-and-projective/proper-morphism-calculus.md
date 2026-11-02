---
article_id: af_e89ce409714107e99d048946
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.properMorphismCalculus
---

# Proper-morphism calculus

Proper morphisms satisfy all clauses of Corollary 4.8: closed immersions are
proper; composites and base changes of proper morphisms are proper; products
over a base are proper; if $g \circ f$ is proper and $g$ is separated, then $f$
is proper; and properness is local on the target.

Separatedness and local finite type satisfy the corresponding
composition and base-change rules. Universal closedness is stable
under composition and base change, and cancels from a composite
against a separated second map by the diagonal argument.
Alternatively, the assertions follow from unique valuation lifts.

## Depends on

- [Proper morphisms](proper-morphism.md)
- [Separated morphisms](../separated-morphisms/separated-morphism.md)

## Proof depends on

- [Valuative criterion for properness](valuative-criterion-proper.md)
- [Separated-morphism calculus](../separated-morphisms/separated-morphism-calculus.md)
- [Finite-type morphisms compose](../first-properties/finite-type-composition.md)
- [Finite type is stable under base extension](../fiber-products/finite-type-base-change.md)
- Composition, base change, and cancellation rules for properness.

## Sources

- [Hartshorne II.4, Corollary 4.8](../../../sources/hartshorne-ii-4.md#properness-and-the-valuative-criterion)
