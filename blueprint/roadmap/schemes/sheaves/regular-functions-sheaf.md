---
article_id: af_5ab88e6586973fd7997b6527
declaration: definition
origin: cited
source_units: [chapter-ii-sections-1-3]
statement: formalized
proof: formalized
lean: Hartshorne.Variety.regularSheaf
---

# The sheaf of regular functions

For a project `Variety X`, package `X.regular U` on every open `U` and the
restriction maps `X.regular_restrict` as a sheaf of commutative rings
`X.regularSheaf`. The sheaf gluing condition is exactly the locality field
`X.regular_of_locally`; pointwise equality gives uniqueness.

The main result is the sheaf definition. It must reuse the Chapter I notion of
regularity so that the comparison of a variety with a scheme on p. 78 does not
introduce a second structure sheaf.

## Depends on

- [Sheaves of abelian groups](sheaves-of-abelian-groups.md)
- [Varieties](../../morphisms/variety.md)

## Proof depends on

- The locality axiom `Hartshorne.Variety.regular_of_locally` carried by the existing variety structure.

## Sources

- [Hartshorne II.1, Example 1.0.1 (p. 62)](../../../sources/hartshorne-ii-1.md#basic-examples-printed-p-62)
