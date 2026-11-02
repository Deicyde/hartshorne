---
article_id: af_6f4cbbd12a16d3bece4d77df
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.InverseSystem.inverseLimit_exact_of_isMittagLeffler
---

# Exactness of inverse limits under Mittag–Leffler

Let

$0 \longrightarrow A n \longrightarrow B n \longrightarrow C n \longrightarrow 0$

be a levelwise short exact sequence of sequential inverse systems. If $A$
satisfies Mittag–Leffler, then

$0 \longrightarrow \lim A \longrightarrow \lim B \longrightarrow \lim C \longrightarrow 0$

is exact.

## Depends on

- [Inverse systems and the Mittag–Leffler condition](inverse-system-mittag-leffler.md)

## Proof depends on

- [Stable-image replacement](mittag-leffler-stable-image.md)
- Left exactness of limits in abelian groups.
- Nonemptiness of the inverse limit of the fibres over a compatible element
  of $\lim C$.

## Sources

- [Hartshorne II.9, Proposition 9.1(b) (p.192)](../../../../sources/hartshorne-ii-9.md#inverse-systems-and-sheaf-limits)
- Stacks Project, tag $0598$.
