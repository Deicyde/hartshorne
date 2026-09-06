---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.isIntegral_of_mul_mem Hartshorne.exists_algebraMap_eq_of_isIntegral Hartshorne.exists_algebraMap_eq_of_mul_mem Hartshorne.fg_projCoordGrading Hartshorne.finiteDimensional_projCoordGrading
---

# An element stabilising a finite-dimensional subspace is integral

If `K` is a `k`-algebra domain, `V ⊆ K` a nonzero finite-dimensional
`k`-subspace, and `f ∈ K` satisfies `f · V ⊆ V`, then `f` is integral over `k`;
and if `k` is algebraically closed, `f` lies in `k`.

This is the content of [Theorem 3.4(a)](projective-global-regular.md) with the
geometry removed. Hartshorne's argument for `𝒪(Y) = k` is that a global regular
function multiplies some graded piece `S(Y)_N` into itself, that piece is a
finite-dimensional `k`-vector space, and `k` is algebraically closed. Only the
first two clauses are about projective varieties.

What makes `f · V ⊆ V` give integrality rather than merely algebraicity is the
determinant trick, and Mathlib supplies it as `IsIntegral.of_mem_of_fg`: it is
enough that `k[f]` be finitely generated as a `k`-module. That holds because
`a ↦ a · v` embeds `k[f]` into `V` for any nonzero `v ∈ V`, injectively because
`K` is a domain. The passage from integral to constant is the minimal polynomial
being irreducible, hence linear over an algebraically closed field.

## The finiteness that feeds it

Each graded piece of `S(Y)` is a finite-dimensional `k`-vector space
(`Hartshorne.finiteDimensional_projCoordGrading`), being the image of a graded
piece of the polynomial ring, and those are finitely generated when there are
finitely many variables.

## Depends on

- [Graded localization](graded-localization.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(a) (pp. 18-19)](../../../sources/hartshorne.md#i3)
