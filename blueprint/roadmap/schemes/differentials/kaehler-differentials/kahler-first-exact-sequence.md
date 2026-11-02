---
article_id: af_01b3b42bdfcfbcdd30757572
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.kaehlerFirstExactSequence
---

# The first exact sequence

For ring maps $A \to B \to C$, the natural sequence of $C$-modules

$C\otimes_B\Omega_{B/A}\longrightarrow\Omega_{C/A}\longrightarrow\Omega_{C/B}\longrightarrow0$

is exact.  The first map sends $c \otimes db$ to $c \cdot db$, and the second forgets
that elements of $B$ may vary over $A$.

## Depends on

- [The universal module of Kähler differentials](kahler-differential-universal.md)

## Proof depends on

- The universal property identifies the kernel at the middle differential module.
- The final map on differential modules is surjective.

## Sources

- [Hartshorne II.8, Proposition 8.3A, printed p. 173](../../../../sources/hartshorne-ii-8.md)
