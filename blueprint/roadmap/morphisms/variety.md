---
declaration: def
origin: cited
---

# Varieties

Over the fixed algebraically closed field `k`, a *variety* is any affine,
quasi-affine, projective or quasi-projective variety, each carrying its regular
functions as defined above.

This is a bookkeeping definition, but it is the one that lets §3 state Theorem
3.2, Proposition 3.5 and Lemma 3.6 for an arbitrary variety `X` while
constraining only `Y`. Getting it wrong forces every later statement to be
quadrupled.

A design decision belongs here rather than in Lean review: whether to define
`Variety` as an inductive sum of the four cases or as a structure bundling a
topological space with a `k`-algebra of regular functions on each open set. The
second is closer to the sheaf-theoretic definition of Chapter II and is likely
to age better, at the cost of proving the four cases satisfy it.

## Depends on

- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)
- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)
- [Regular functions on a quasi-projective variety](regular-function-quasi-projective.md)

## Sources

- [Hartshorne I.3, definition of a variety over `k` (p. 15)](../../sources/hartshorne.md#i3)
