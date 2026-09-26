---
article_id: af_267625a760ca87aba736c835
declaration: theorem
origin: bridged
source_units: [theorem-i-3-9a]
statement: formalized
proof: formalized
lean: Hartshorne.moduleFinite_integralClosure_of_isPurelyInseparable Hartshorne.algebraMap_integralClosure_surjective_of_charZero Hartshorne.moduleFinite_integralClosure_of_isPurelyInseparable_of_charP Hartshorne.exists_frobeniusExponent_and_fin_spanningFamily_integralClosure_of_charP
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

## Provenance

Stacks Project, Tag 0335 implies the stated finiteness as part of the stronger
Nagata theorem, but it does not supply the displayed Frobenius-spanning proof.
That proof specification is project-authored. This remains a bridge article
because it isolates the inseparable intermediate step rather than a direct
Hartshorne target.

## Depends on

No project-local statement prerequisites.

## Proof depends on

- [Frobenius is finite on an affine algebra over a perfect field](frobenius-finite-affine-algebra.md)

## Sources

- [Project-authored proof specification for Hartshorne I.3.9A](../../sources/hartshorne.md#project-authored-proof-specification-for-theorem-i39a)
- [Stacks Project, finite-type algebras over fields are Nagata (Tag 0335)](https://stacks.math.columbia.edu/tag/0335)
- [Stacks Project, Japanese and N-2 rings (Tag 032F)](https://stacks.math.columbia.edu/tag/032F)
