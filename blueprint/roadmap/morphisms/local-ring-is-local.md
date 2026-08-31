---
declaration: instance
origin: cited
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

## Depends on

- [The local ring at a point](local-ring.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, the local ring property of `𝒪_{P,Y}` and its residue field (p. 16)](../../sources/hartshorne.md#i3)
