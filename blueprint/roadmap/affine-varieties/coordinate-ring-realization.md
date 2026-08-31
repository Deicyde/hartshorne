---
declaration: theorem
origin: cited
---

# Every finitely generated domain is a coordinate ring

Any finitely generated `k`-algebra `B` that is an integral domain is isomorphic
to `A(Y)` for some affine variety `Y`. Writing `B` as a quotient
`A/𝔞` of a polynomial ring `A = k[x₁,…,xₙ]`, the variety is `Y = Z(𝔞)`.

Hartshorne records this as the second half of Remark 1.4.6 and does not belabour
it, but it carries the two facts that make the construction work. That `B` is a
domain makes `𝔞` prime, which makes `Z(𝔞)` irreducible and therefore a variety.
That `𝔞` is prime makes it radical, so the Nullstellensatz gives `I(Z(𝔞)) = 𝔞`
rather than merely `√𝔞`, and hence `A(Y) = A/I(Z(𝔞)) = A/𝔞 ≅ B`.

Both steps fail without the domain hypothesis, which is the reason it appears in
the statement of Corollary 3.8 rather than being dropped for a general finitely
generated `k`-algebra. This article exists separately from the coordinate ring
construction because it is what supplies essential surjectivity in that
corollary, and a functor being essentially surjective is a theorem that wants
its own name.

## Depends on

- [The affine coordinate ring](affine-coordinate-ring.md)
- [Affine and quasi-affine varieties](affine-variety.md)

## Proof depends on

- [Algebraic sets and radical ideals](radical-ideal-correspondence.md)
- [Hilbert's Nullstellensatz](nullstellensatz.md)

## Sources

- [Hartshorne I.1, Remark 1.4.6 (pp. 4-5)](../../sources/hartshorne.md#i1)
