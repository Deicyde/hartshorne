---
declaration: abbrev
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.coordinateRing Hartshorne.finiteType_coordinateRing Hartshorne.isDomain_coordinateRing
---

# The affine coordinate ring

For an affine algebraic set `Y ⊆ 𝔸ⁿ`, the *affine coordinate ring* is
`A(Y) = A/I(Y)`.

When `Y` is a variety, `I(Y)` is prime, so `A(Y)` is a finitely generated
`k`-algebra that is an integral domain. That much is this node: the construction
and the two structural facts it carries.

Hartshorne's converse in Remark 1.4.6 — every finitely generated `k`-algebra
domain arises this way — is the harder half and is
[its own article](coordinate-ring-realization.md), because it is a theorem rather
than part of the construction and because the equivalence of categories in §3
cites it separately.

## Depends on

- [The vanishing ideal](vanishing-ideal.md)
- [Affine and quasi-affine varieties](affine-variety.md)

## Proof depends on

- [Algebraic sets and radical ideals](radical-ideal-correspondence.md)

## Sources

- [Hartshorne I.1, definition of `A(Y)` and Remark 1.4.6 (pp. 4-5)](../../sources/hartshorne.md#i1)
