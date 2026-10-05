---
article_id: af_765586c14a163cbbdb9f9f40
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
statement: formalized
proof: formalized
lean: Hartshorne.sectionSupport Hartshorne.sheafSupport Hartshorne.isClosed_sectionSupport
---

# The support of a section is closed

For a section `s ∈ F(U)`, its support
`{x ∈ U | germ_x(s) ≠ 0}` is closed in `U`.

The section-support and sheaf-support definitions are supporting declarations:
the latter is `{x ∈ X | Fₓ ≠ 0}` and need not be closed in general.
Proposition 5.9 later uses that definition for `O_X/F`. The unique main
artifact of this node is the closedness theorem for a section's support.
Focused search found only specialized Mathlib supports, not this generic
sheaf API.

## Depends on

- [Stalks and germs](../sheaves/stalks-and-germs.md)

## Proof depends on

- Equality of germs after restricting to a sufficiently small neighbourhood.

## Sources

- [Hartshorne II.1, Exercise 1.14 (p. 67), used on p. 116](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)
