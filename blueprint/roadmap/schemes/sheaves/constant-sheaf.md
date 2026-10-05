---
article_id: af_f1362ef3c0165cf18af55a36
declaration: definition
origin: cited
source_units: [chapter-ii-sections-1-3]
statement: formalized
proof: formalized
lean: Hartshorne.constantSheaf
---

# The constant sheaf

For an abelian group `A`, define the constant sheaf on `X` by assigning to an
open `U` the additive group of continuous maps from `U` to `A` with the
discrete topology. Restrictions are precomposition with inclusions, and
continuous maps glue pointwise.

Mathlib's `CategoryTheory.constantSheaf` is the sheafification of the constant
presheaf, while `TopCat.sheafToTop` provides the underlying Type-valued
continuous-map sheaf. The main project declaration supplies Hartshorne's
explicit AddCommGrp-valued presentation; it should not claim an upstream exact
match until a comparison with the abstract constant sheaf is proved.

## Depends on

- [Sheaves of abelian groups](sheaves-of-abelian-groups.md)

## Proof depends on

- Mathlib's sheaf of continuous maps and algebraic structure on locally constant functions.

## Sources

- [Hartshorne II.1, Example 1.0.3 (p. 62)](../../../sources/hartshorne-ii-1.md#basic-examples-printed-p-62)

