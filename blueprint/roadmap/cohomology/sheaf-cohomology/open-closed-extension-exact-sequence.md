---
article_id: af_51775dda22df3e41da103fae
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.openClosedExtensionSequence_shortExact Hartshorne.openClosedExtensionSequence
---

# The open–closed extension exact sequence

Let $i : Y \hookrightarrow X$ be closed, let $j : U \hookrightarrow X$ be its open complement, and let
$F$ be an abelian sheaf on $X$. There is a natural short exact sequence

$0 \longrightarrow j_!(F|_U) \longrightarrow F \longrightarrow i_*(F|_Y) \longrightarrow 0$.

Here $F|_U = j^{-1}F$ and $F|_Y = i^{-1}F$ are inverse images. The first map is the
counit of the adjunction between $j_!$ and $j^{-1}$, and the second is the unit of the
adjunction between $i^{-1}$ and $i_*$; both are natural in $F$.

This is the supporting result deferred from II.1.19(c); the main artifact is
the natural short exact sequence, proved stalkwise.

## Depends on

- [Open extension by zero](../../schemes/sheaf-functors/open-extension-by-zero.md)
- [Closed extension by zero](../../schemes/sheaf-functors/closed-extension-by-zero.md)

## Proof depends on

- [Exactness is detected on stalks](../../schemes/sheaves/stalkwise-exactness.md)

## Sources

- [Hartshorne II.1.19(c) as adopted for III.2](../../../sources/hartshorne-iii-1-2.md#filtered-colimits-and-closed-support-printed-pp-208210)
