---
article_id: af_29f475baa591ec20b277f792
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.kaehlerConormal_rightExact
---

# The conormal exact sequence

Let $B$ be an $A$-algebra, let $I \subseteq B$, and put $C = B/I$.  The canonical
sequence

$I/I^2\longrightarrow C\otimes_B\Omega_{B/A}\longrightarrow\Omega_{C/A}\longrightarrow0$

is exact, with the first map carrying the class of $b \in I$ to $1 \otimes db$.
No injectivity assertion is made at the left end.

## Depends on

- [The universal module of Kähler differentials](kahler-differential-universal.md)

## Proof depends on

- The universal property of differentials gives exactness at the middle term.
- Every differential in the quotient algebra lifts, giving surjectivity of the final map.

## Sources

- [Hartshorne II.8, Proposition 8.4A, printed p. 173](../../../../sources/hartshorne-ii-8.md)
