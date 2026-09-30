---
article_id: af_4b49ee4a3033d8c3e5250ee9
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
---

# Multiplicity in a graded prime filtration

For a prime `p` minimal over `Ann M`, define the multiplicity of `M` at `p` by

`μ_p(M) = Module.length (S_p) (M_p)`.

Keep this value in Mathlib's `ℕ∞` until finiteness is proved. For every graded
prime filtration of `M`, it is finite and equals the number of indices `i` for
which the factor prime `pᵢ` is `p`. The sole main result is planned as
`Hartshorne.gradedPrimeFiltration_multiplicity_eq_count`; the supporting
definition is `Hartshorne.gradedMultiplicity`.

After localizing the filtration at `p`, a factor associated to `pᵢ` vanishes
unless `pᵢ ⊆ p`. Minimality and the preceding support theorem turn that
containment into equality. Every surviving factor is the residue field of the
local ring `S_p`, hence has length one, and additivity of module length counts
the occurrences. This also proves that the definition is independent of the
chosen filtration.

## Depends on

- [Graded prime filtrations](graded-prime-filtration.md)
- [Minimal primes in a graded prime filtration](prime-filtration-support.md)

## Sources

- [Hartshorne I.7, multiplicity definition and Proposition 7.4(b) (p. 51)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
