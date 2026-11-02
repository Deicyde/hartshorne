---
article_id: af_680755a0596316cf89003ad4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_closedExtensionByZeroStalkIsos
---

# Closed extension by zero

Let $i : Z \hookrightarrow X$ be the inclusion of a closed subspace and $F$ a sheaf of
abelian groups on $Z$. Show that direct image is extension by zero:

$(i_*F)_{x} \cong F_{x}$ for $x \in Z$, and $(i_*F)_{x} \cong 0$ for $x \notin Z$.

At a point of $Z$, neighbourhoods in $X$ restrict to neighbourhoods
in $Z$, giving the stalk comparison. Outside $Z$, the open
complement is a neighbourhood on which the direct image has zero
sections.

## Depends on

- [Direct image of a sheaf](direct-image.md)
- [Stalks and germs](../sheaves/stalks-and-germs.md)

## Proof depends on

- [Sheaves of abelian groups](../sheaves/sheaves-of-abelian-groups.md), for zero sections on the empty open.

## Sources

- [Hartshorne II.1, Exercise 1.19(a) (p. 68), used on p. 196](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)
