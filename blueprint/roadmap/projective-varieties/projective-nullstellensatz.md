---
declaration: theorem
origin: cited
---

# The homogeneous Nullstellensatz

Let `𝔞 ⊆ S` be a homogeneous ideal and `f ∈ S` homogeneous with `deg f > 0`. If
`f(P) = 0` for every `P ∈ Z(𝔞)` then `f^q ∈ 𝔞` for some `q > 0` (Exercise 2.1).

The proof reduces to the affine Nullstellensatz through the cone: interpret `S`
as the coordinate ring of `𝔸ⁿ⁺¹` and observe that the affine zero set of `𝔞` is
the cone over `Z(𝔞)` together with the origin. The degree hypothesis is what
handles the origin, and it is also why the statement must fail for degree-zero
`f`.

The companion fact, Exercise 2.2, is worth proving here: `Z(𝔞) = ∅` if and only
if `√𝔞` is `S` or the irrelevant ideal `S₊ = ⨁_{d>0} S_d`, equivalently
`𝔞 ⊇ S_d` for some `d > 0`. That is the statement the ideal correspondence needs
in order to know which homogeneous radical ideals to exclude.

## Depends on

- [The homogeneous vanishing ideal](homogeneous-vanishing-ideal.md)

## Proof depends on

- [Hilbert's Nullstellensatz](../affine-varieties/nullstellensatz.md)
- [Algebraic sets](../affine-varieties/algebraic-set.md)

## Sources

- [Hartshorne I.2, Exercises 2.1 and 2.2 (p. 11)](../../sources/hartshorne.md#i2)
