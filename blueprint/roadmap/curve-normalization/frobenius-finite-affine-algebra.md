---
article_id: af_c443fb28d7ae4626b5a146aa
declaration: theorem
origin: bridged
source_units: [theorem-i-3-9a]
statement: formalized
proof: formalized
lean: Hartshorne.moduleFinite_frobeniusPowerSubalgebra Hartshorne.frobeniusPowerHom_finite Hartshorne.iterateFrobenius_finite
---

# Frobenius is finite on an affine algebra over a perfect field

Let `k` be a perfect field of positive characteristic `p`, let `A` be a
finitely generated `k`-algebra, and let `q = p^e`. Then `A` is a finite module
over its subring of `q`th powers `A^q`.

Choose finite algebra generators `a₁,…,aₙ`. Perfection of `k` puts every
coefficient in `k` in the image of the `q`th-power map. Reducing each exponent
modulo `q` shows that the finitely many monomials

`a₁^r₁ ⋯ aₙ^rₙ`, with every `rᵢ < q`,

span `A` over `A^q`. Package the result both for the range of the iterated
Frobenius homomorphism and for the corresponding scalar-restriction module;
the inseparable-normalization argument needs to move between those two forms.

## Provenance

Stacks Project, Tag 0CCD proves that relative Frobenius is finite for a
locally finite-type morphism in positive characteristic. Over a perfect base
field, the image of the corresponding affine ring map is the subring of
`p`th powers; iteration gives the stated `q`th-power result. The iterated-range
and scalar-restriction API packaging is project-authored. This remains a
bridge article because it is an intermediate input to Hartshorne's theorem,
not a direct source target.

## Depends on

No project-local statement prerequisites.

## Sources

- [Project-authored proof specification for Hartshorne I.3.9A](../../sources/hartshorne.md#project-authored-proof-specification-for-theorem-i39a)
- [Stacks Project, relative Frobenius is finite (Tag 0CCD)](https://stacks.math.columbia.edu/tag/0CCD)
