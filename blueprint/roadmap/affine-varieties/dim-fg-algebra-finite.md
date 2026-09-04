---
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.exists_ringKrullDim_eq_natCast Hartshorne.finiteRingKrullDim_of_finiteType
---

# A finitely generated algebra over a field has finite dimension

Let `k` be a field and `R` a nontrivial finitely generated `k`-algebra. Then
`dim R` is a natural number: there is an `s` with `dim R = s`, so `dim R` is
neither `⊥` nor `⊤`.

Noether normalisation presents `R` as an injective integral extension of a
polynomial ring `k[y₁,…,y_s]`. Dimension is invariant under such extensions, and
`dim k[y₁,…,y_s] = s`, so `dim R = s`.

This is the half of Theorem 1.8A that does not need transcendence degree, and it
is the half that gets used silently. Because `ringKrullDim` is valued in
`WithBot ℕ∞`, every numerical statement in §1 and §3 is an equation in that
type, and arguments that add, subtract or compare dimensions need to know the
values are finite before they mean anything. Recording it as
`FiniteRingKrullDim` makes Mathlib's own finite-dimension API available.

It is stated for a finitely generated algebra rather than a domain: neither
Noether normalisation nor the integral-extension argument needs a domain, and
the coordinate ring of a reducible algebraic set is not one.

## Mathlib boundary

Noether normalisation is `exists_integral_inj_algHom_of_fg`, and
`MvPolynomial.ringKrullDim_of_isNoetherianRing` gives the polynomial ring. Note
that `MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing` in
`RingTheory/KrullDimension/Basic.lean` is still a `proof_wanted`; the result is
available under the other name, over an arbitrary finite index type.

## Depends on

- [Krull dimension is invariant under integral extensions](dimension-integral-extension.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)
