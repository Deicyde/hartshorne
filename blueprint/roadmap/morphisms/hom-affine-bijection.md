---
declaration: theorem
origin: cited
---

# Morphisms into an affine variety

Let `X` be any variety and `Y` an affine variety. Then there is a natural
bijection

`α : Hom(X, Y) → Hom_{k-alg}(A(Y), 𝒪(X))` (Proposition 3.5),

where the left side is morphisms of varieties and the right side is `k`-algebra
homomorphisms.

Forward, a morphism pulls regular functions back, and `𝒪(Y) ≅ A(Y)` by Theorem
3.2. Backward, given `h : A(Y) → 𝒪(X)`, write `Y ⊆ 𝔸ⁿ`, let `x̄ᵢ` be the image of
`xᵢ` in `A(Y)`, and set `ψ(P) = (h(x̄₁)(P), …, h(x̄ₙ)(P))`. Its image lands in `Y`
because any `f ∈ I(Y)` satisfies `f(ψ(P)) = h(f)(P) = 0`, and it is a morphism by
Lemma 3.6.

Naturality in both arguments is worth proving here even though Hartshorne does
not spell it out, since the equivalence of categories two nodes later needs the
bijection to be a natural isomorphism rather than a family of bijections.

## Depends on

- [Morphisms](morphism.md)
- [The ring of regular functions](ring-of-regular-functions.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Proof depends on

- [The coordinate ring is the ring of regular functions](global-regular-eq-coordinate-ring.md)
- [Criterion for a morphism into an affine variety](morphism-to-affine-criterion.md)

## Sources

- [Hartshorne I.3, Proposition 3.5 (p. 19)](../../sources/hartshorne.md#i3)
