---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_pow_mem_of_forall_homogeneousVanish Hartshorne.zeroSet_smul_of_isHomogeneousIdeal Hartshorne.eval_zero_of_isHomogeneous
---

# The homogeneous Nullstellensatz

Let `𝔞 ⊆ S` be a homogeneous ideal and `f ∈ S` homogeneous with `deg f > 0`. If
`f(P) = 0` for every `P ∈ Z(𝔞)` then `f^q ∈ 𝔞` for some `q > 0` (Exercise 2.1).

The proof reduces to the affine Nullstellensatz through the cone: interpret `S`
as the coordinate ring of `𝔸ⁿ⁺¹` and observe that the affine zero set of `𝔞` is
the cone over `Z(𝔞)` together with the origin. The degree hypothesis is what
handles the origin, and it is also why the statement must fail for degree-zero
`f`.

The step that makes the reduction work, and that Hartshorne's hint leaves
implicit, is that the affine zero set of a homogeneous ideal is stable under
scaling. Without it a nonzero affine zero cannot be read as a point of `Z(𝔞)`,
because the projective point carries an arbitrary representative rather than the
affine point one started with.

Exercise 2.2, which characterises when `Z(𝔞) = ∅` in terms of the irrelevant
ideal, is not proved here. It is needed only to decide which homogeneous radical
ideals the correspondence must exclude, so it belongs with
[that article](homogeneous-ideal-correspondence.md) and is recorded there.

## Depends on

- [The homogeneous vanishing ideal](homogeneous-vanishing-ideal.md)

## Proof depends on

- [Hilbert's Nullstellensatz](../affine-varieties/nullstellensatz.md)
- [Algebraic sets](../affine-varieties/algebraic-set.md)
- [Homogeneous ideals](homogeneous-ideal.md)

## Sources

- [Hartshorne I.2, Exercise 2.1 (p. 11)](../../sources/hartshorne.md#i2)
