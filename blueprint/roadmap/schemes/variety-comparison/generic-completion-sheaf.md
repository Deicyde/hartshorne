---
article_id: af_a8a434c4482ee7dabb0f9d61
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.genericCompletionRegularSheaf Hartshorne.genericCompletionRegularSheaf_obj_eq_pushforward Hartshorne.genericCompletionRegularSectionsEquiv Hartshorne.genericCompletionRegularSectionsEquiv_restrict Hartshorne.genericCompletionRegularSectionsNatIso
---

# The regular-function sheaf on the generic completion

For a project variety $V$, transport its sheaf of regular functions across the
open-set order isomorphism between the open subsets of $V$ and $t(V)$.  Equivalently, define the
structure sheaf on $t(V)$ as $\alpha _{V\cdot }\mathcal{O} _V$.

The sheaf condition follows from locality of regular functions.
Restriction maps are their usual restrictions, and sections on
corresponding open subsets identify canonically.

## Depends on

- [The generic-completion functor](generic-completion.md)
- [Ring of regular functions](../../morphisms/ring-of-regular-functions.md)

## Sources

- [Hartshorne II.2, the ringed space $(t(V), \alpha _*\mathcal{O} _V)$ (p. 78)](../../../sources/hartshorne-ii-2.md#schemes-over-a-base-and-proposition-26)
