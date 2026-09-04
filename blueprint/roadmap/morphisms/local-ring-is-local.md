---
declaration: instance
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.instIsLocalRingLocalRingAt Hartshorne.instCommRingLocalRingAt Hartshorne.evalAtPoint Hartshorne.isUnit_iff_evalAtPoint_ne_zero Hartshorne.maximalIdeal_eq_ker Hartshorne.residueFieldEquiv Hartshorne.GermRep.inv
---

# The local ring is local

`𝒪_{P,Y}` is a local ring. Its unique maximal ideal `𝔪` is the set of germs
vanishing at `P`, and the residue field `𝒪_P/𝔪` is isomorphic to `k`.

The argument is one line in Hartshorne and one line in Lean once the germ
construction exists: if `f(P) ≠ 0` then `f` is nonzero on some neighbourhood of
`P`, so `1/f` is regular there and the germ of `f` is a unit. Hence every
non-unit lies in `𝔪`, which is exactly the condition for a local ring. The
residue field is `k` because evaluation at `P` is a surjection `𝒪_P → k` with
kernel `𝔪`.

Separated from the germ construction because it is the `IsLocalRing` instance
that everything downstream actually uses: Theorem 3.2(c) compares it with
`A(Y)_{𝔪_P}` and reads `dim 𝒪_P` as `height 𝔪_P`, and Theorem 3.4(b) does the
same against `S(Y)_(𝔪_P)`. Neither comparison can be stated without knowing
which ideal is maximal.

## What the ring structure cost

Hartshorne says `𝒪_P` "is a ring" and moves on. In Lean the operations have to
be built, and they land in this node rather than in the germ construction
because nothing before this needed them. Addition and multiplication intersect
the domains of two representatives, which is legitimate exactly because both
contain `P`: no irreducibility is needed to know the intersection is nonempty,
unlike the corresponding step for `K(Y)`. Every ring axiom then reduces to the
same identity in `k`, checked at a point of the common domain.

Two supporting facts are not in Hartshorne's line and are not in Mathlib:
a nowhere-zero regular function has a regular reciprocal, obtained by exchanging
numerator and denominator, and the set where a regular function is nonzero is
open, which is Lemma 3.1 applied to the pair `(f, 0)`.

## Depends on

- [The local ring at a point](local-ring.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, the local ring property of `𝒪_{P,Y}` and its residue field (p. 16)](../../sources/hartshorne.md#i3)
