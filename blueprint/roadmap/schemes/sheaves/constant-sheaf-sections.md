---
article_id: af_deb2840446acccc594f3bf7f
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
statement: formalized
proof: formalized
lean: Hartshorne.exists_constantSheafSectionsEquivOfIsPreconnected Hartshorne.exists_constantSheafSectionsEquivConnectedComponents
---

# Sections of a constant sheaf

Let `A_X` be the constant sheaf associated to `A`. If `U` is a connected
nonempty open subset of `X`, evaluation at any chosen point gives an additive
equivalence `A_X(U) ≃+ A`. More generally, if the connected components of `U`
are open, restriction gives an additive equivalence between `A_X(U)` and the
product of copies of `A` indexed by those components.

The nonemptiness is explicit because Lean's connected-space API distinguishes
it from preconnectedness and the empty open has the zero group of sections.

## Depends on

- [The constant sheaf](constant-sheaf.md)

## Proof depends on

- Mathlib's `LocallyConstant.apply_eq_of_isPreconnected` and the open-component decomposition.

## Sources

- [Hartshorne II.1, constant-sheaf section computations in Example 1.0.3 (p. 62)](../../../sources/hartshorne-ii-1.md#basic-examples-printed-p-62)

