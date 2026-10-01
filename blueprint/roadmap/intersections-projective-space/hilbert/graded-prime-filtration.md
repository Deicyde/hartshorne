---
article_id: af_cf06bb1e31416a59c82e0a20
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.exists_gradedPrimeFiltration
---

# Graded prime filtrations

Let `S` be a Noetherian integer-graded ring and let `M` be a finite
integer-graded `S`-module. There is a finite increasing filtration by
homogeneous submodules

`0 = M₀ ⊆ M₁ ⊆ ⋯ ⊆ Mₜ = M`

such that, for every `i`, the graded quotient `Mᵢ/Mᵢ₋₁` is
graded-equivalent to `(S/pᵢ)(lᵢ)` for a homogeneous prime ideal `pᵢ` and an
integer `lᵢ`. The sole main declaration is planned as
`Hartshorne.exists_gradedPrimeFiltration`.

Package the filtration as a finite relational series whose steps contain the
prime, shift, and graded equivalence. This lets later nodes inspect factors
without choosing a second list. The proof takes a maximal already-filtered
homogeneous submodule. In the graded quotient, choose a nonzero homogeneous
element with maximal annihilator; its annihilator is prime, and adjoining its
cyclic submodule extends the filtration unless it was already all of `M`.

Pinned Mathlib's
`IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime` is the exact
ungraded analogue, but it does not preserve homogeneous submodules or record
twists and therefore is prior art rather than an upstream solution.

## Depends on

- [Integer-graded submodules and quotients](graded-submodules-and-quotients.md)
- [Homogeneous annihilators and cyclic modules](graded-annihilator.md)

## Sources

- [Hartshorne I.7, existence clause of Proposition 7.4 (pp. 50–51)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
