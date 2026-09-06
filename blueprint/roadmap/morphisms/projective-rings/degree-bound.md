---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.mk_X_eq_zero_of_inter_eq_empty Hartshorne.exists_le_of_degree_le Hartshorne.monomial_eq_mul_X_pow Hartshorne.degree_sub_single Hartshorne.gradedImage Hartshorne.mul_mem_gradedImage
---

# The degree bound

If `t` lies in the fraction field of `S(Y)` and `xᵢ^{Nᵢ} · t ∈ S(Y)` for every
chart `Uᵢ` meeting `Y`, then `t · S(Y)_N ⊆ S(Y)_N` for any `N` at least the sum
of the `Nᵢ`.

This is Hartshorne's "let `N ≥ Σ Nᵢ`" in the proof of
[Theorem 3.4(a)](projective-global-regular.md). It is the only combinatorial
step in that part and the only place the cover being finite is used.

## The pigeonhole

`S(Y)_N` is spanned by classes of degree-`N` monomials, so it is enough to treat
`x^α`, and there are two cases.

If some `αᵢ > 0` with `Y ∩ Uᵢ` empty, then `xᵢ` vanishes on `Y`, the class of
`x^α` is zero, and there is nothing to check. Otherwise `α` is supported on the
charts that meet `Y`, and `Σ αᵢ = N ≥ Σ Nᵢ` over those forces `αᵢ ≥ Nᵢ` for some
`i`; then `x^α` absorbs the denominator and `x^α · t = (x^α/xᵢ^{Nᵢ}) · gᵢ` has
degree `(N − Nᵢ) + Nᵢ`.

The two cases are what makes the hypothesis "for every chart meeting `Y`" rather
than "for every chart" the right one: the charts that miss `Y` contribute
nothing because their variables are already zero in `S(Y)`.

## Depends on

- [Graded localization](graded-localization.md)
- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(a) (pp. 18-19)](../../../sources/hartshorne.md#i3)
