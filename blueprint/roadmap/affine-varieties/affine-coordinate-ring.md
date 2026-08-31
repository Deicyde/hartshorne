---
declaration: def
origin: cited
---

# The affine coordinate ring

For an affine algebraic set `Y ⊆ 𝔸ⁿ`, the *affine coordinate ring* is
`A(Y) = A/I(Y)`.

When `Y` is a variety, `I(Y)` is prime, so `A(Y)` is a finitely generated
`k`-algebra that is an integral domain. Hartshorne notes the converse in Remark
1.4.6: any finitely generated `k`-algebra domain `B` is `A(Y)` for some affine
variety `Y`, obtained by writing `B = A/𝔞` and taking `Y = Z(𝔞)`. Both
directions belong in this node, since §3 needs them to state the equivalence of
categories.

The interesting half is the converse: it needs `𝔞` prime to give `Z(𝔞)`
irreducible, which is the correspondence from the previous node, and it needs
`I(Z(𝔞)) = 𝔞` rather than merely `√𝔞`, which is the Nullstellensatz plus
primeness.

## Depends on

- [The vanishing ideal](vanishing-ideal.md)
- [Affine and quasi-affine varieties](affine-variety.md)

## Proof depends on

- [Algebraic sets and radical ideals](radical-ideal-correspondence.md)

## Sources

- [Hartshorne I.1, definition of `A(Y)` and Remark 1.4.6 (pp. 4-5)](../../sources/hartshorne.md#i1)
