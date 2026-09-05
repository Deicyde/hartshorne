---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.evalAt Hartshorne.maximalIdealAt Hartshorne.maximalIdealAt_isMaximal Hartshorne.maximalIdealAt_injective Hartshorne.maximalIdealAt_surjective Hartshorne.pointsEquivMaximalIdeals Hartshorne.residueEquiv
---

# Points and maximal ideals

For an affine algebraic set `Y`, sending `P` to the ideal `𝔪_P` of functions
vanishing at `P` is a bijection from the points of `Y` to the maximal ideals of
`A(Y)` (Theorem 3.2(b)).

Evaluation at `P` descends to `A(Y)`, because every element of `I(Y)` vanishes
at `P`, and is surjective onto `k`, so its kernel `𝔪_P` is maximal and the
residue field is `k`. Injectivity is the separation of distinct points by a
coordinate function. Surjectivity is the Nullstellensatz: a maximal ideal of
`A(Y)` pulls back to a maximal ideal of `k[x₁,…,xₙ]`, which is the ideal of a
point, and that point lies in `Z(I(Y)) = Y`.

Split from the rest of Theorem 3.2 because it is the one part that needs
nothing else in §3 and because two later results consume it directly: Theorem
3.2(a) uses it to show an ideal of denominators is the whole ring, and Theorem
3.2(c) is stated about the localisation at `𝔪_P`.

Stated for an algebraic set rather than a variety: nothing in the argument uses
irreducibility.

## Depends on

- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Proof depends on

- [The Nullstellensatz](../affine-varieties/nullstellensatz.md)
- [Algebraic sets and radical ideals](../affine-varieties/radical-ideal-correspondence.md)

## Sources

- [Hartshorne I.3, Theorem 3.2(b) (p. 17)](../../sources/hartshorne.md#i3)
