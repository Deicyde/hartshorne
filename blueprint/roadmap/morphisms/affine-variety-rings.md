---
declaration: theorem
origin: cited
---

# The rings of an affine variety

Let `Y ⊆ 𝔸ⁿ` be an affine variety with coordinate ring `A(Y)`. Then
(Theorem 3.2):

- `𝒪(Y) ≅ A(Y)`;
- `P ↦ 𝔪_P` is a bijection from the points of `Y` to the maximal ideals of
  `A(Y)`, where `𝔪_P` is the ideal of functions vanishing at `P`;
- `𝒪_P ≅ A(Y)_{𝔪_P}`, and `dim 𝒪_P = dim Y`;
- `K(Y)` is the fraction field of `A(Y)`, a finitely generated field extension of
  `k` of transcendence degree `dim Y`.

Everything follows from the injection `α : A(Y) → 𝒪(Y)` plus the correspondence
of §1. The bijection on points is Corollary 1.4 pushed through the quotient;
`𝒪_P ≅ A(Y)_{𝔪_P}` is injectivity of `α` plus surjectivity straight from the
definition of regular; the dimension claim is `dim 𝒪_P = height 𝔪_P` together
with Theorem 1.8A. Part (a) is last and is the only one needing an outside fact:
a domain is the intersection of its localizations at all maximal ideals, taken
inside its fraction field.

This is the main theorem of the section. It says the coordinate ring already
knows everything about an affine variety, and it is what makes the equivalence of
categories at the end of the chapter possible.

## Depends on

- [The ring of regular functions](ring-of-regular-functions.md)
- [The local ring at a point](local-ring.md)
- [The function field](function-field.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Proof depends on

- [Algebraic sets and radical ideals](../affine-varieties/radical-ideal-correspondence.md)
- [Dimension is the dimension of the coordinate ring](../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [Dimension of a finitely generated domain](../affine-varieties/dim-fg-domain.md)

## Sources

- [Hartshorne I.3, Theorem 3.2 (p. 17)](../../sources/hartshorne.md#i3)
