---
declaration: theorem
origin: cited
---

# Algebraic sets and homogeneous radical ideals

`Y ↦ J(Y)` and `𝔞 ↦ Z(𝔞)` are mutually inverse, inclusion-reversing bijections
between the algebraic sets of `ℙⁿ` and the homogeneous radical ideals of `S`
other than the irrelevant ideal `S₊`. An algebraic set is irreducible if and
only if its homogeneous ideal is prime, and `ℙⁿ` itself is irreducible
(Exercise 2.4).

This is the projective form of Corollary 1.4, and the proof follows it once the
homogeneous Nullstellensatz supplies `J(Z(𝔞)) = √𝔞` for `Z(𝔞) ≠ ∅`. The
irreducible-iff-prime half uses that primeness of a homogeneous ideal can be
tested on homogeneous elements, which is why the graded background node comes
first.

The exclusion of `S₊` is the one genuine difference from the affine case and the
usual source of off-by-one errors: `S₊` is a homogeneous radical ideal with
`Z(S₊) = ∅`, and `∅` already corresponds to `S`.

Exercise 2.2 belongs here rather than with the Nullstellensatz: `Z(𝔞) = ∅` if
and only if `√𝔞` is `S` or `S₊`, equivalently `𝔞 ⊇ S_d` for some `d > 0`. That
is exactly the criterion deciding which homogeneous radical ideals this
correspondence must leave out, and it is not needed to prove Exercise 2.1.

## Depends on

- [The homogeneous vanishing ideal](homogeneous-vanishing-ideal.md)
- [The homogeneous Nullstellensatz](projective-nullstellensatz.md)
- [Homogeneous ideals](homogeneous-ideal.md)

## Sources

- [Hartshorne I.2, Exercise 2.4 (p. 11)](../../sources/hartshorne.md#i2)
