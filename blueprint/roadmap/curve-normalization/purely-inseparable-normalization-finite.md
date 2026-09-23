---
article_id: af_267625a760ca87aba736c835
declaration: theorem
origin: bridged
source_units: [theorem-i-3-9a]
---

# Purely inseparable normalizations are finite

Let `k` be an algebraically closed field, let `A` be a finitely generated,
integrally closed `k`-algebra domain with fraction field `K`, and let `L/K` be
a finite purely inseparable field extension.  Then the integral closure of
`A` in `L` is a finite `A`-module.

This is the inseparable step missing from Mathlib's integral-closure
finiteness theorem. In characteristic zero the extension is trivial. In
characteristic `p`, choose `q = p^e` with `L^q ⊆ K`. If `B` is the integral
closure and `z ∈ B`, then `z^q ∈ K` is integral over `A`, hence belongs to `A`
by normality. Because `k` is perfect and `A` is finite type, `A` is finite over
its Frobenius image `A^q`. Thus the `A^q`-submodule `B^q ⊆ A` is finitely
generated, say by `b₁^q,…,bₙ^q`. Every `b ∈ B` then satisfies
`b^q = ∑ aᵢ^q bᵢ^q = (∑ aᵢ bᵢ)^q`; injectivity of Frobenius in the field `L`
shows that the `bᵢ` span `B` over `A`.

Keep the exponent and the finite spanning family explicit.  They are needed
when the result is applied after taking the maximal separable subextension of
an arbitrary finite extension.

## Depends on

No project-local statement prerequisites.

## Proof depends on

- [Frobenius is finite on an affine algebra over a perfect field](frobenius-finite-affine-algebra.md)

## Sources

- [Hartshorne I.3, Theorem 3.9A (p. 20)](../../sources/hartshorne.md#i3)
