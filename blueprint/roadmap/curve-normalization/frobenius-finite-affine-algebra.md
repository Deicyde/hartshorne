---
article_id: af_c443fb28d7ae4626b5a146aa
declaration: theorem
origin: bridged
source_units: [theorem-i-3-9a]
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

## Depends on

No project-local statement prerequisites.

## Sources

- [Hartshorne I.3, algebraic input to Theorem 3.9A (p. 20)](../../sources/hartshorne.md#i3)
- [Stacks Project, finite-type algebras over fields are Nagata (Tag 0335)](https://stacks.math.columbia.edu/tag/0335)
