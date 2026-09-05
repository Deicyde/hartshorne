---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.homEquivAlgHom Hartshorne.homToAlgHom Hartshorne.algHomToHom Hartshorne.algHomToFun Hartshorne.eval_algHomToFun
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

Naturality in both arguments is not part of this node. Hartshorne does not spell
it out, and the equivalence of categories does need the bijection to be natural
rather than a family of bijections, so it is proved
[there](affine-variety-equivalence.md), where the functors it is natural in
exist. Proving it here would mean stating those functors here.

## The bijection does not need Theorem 3.2(a)

Hartshorne phrases the forward map as "pull back regular functions, then apply
`𝒪(Y) ≅ A(Y)`", which reads as a dependency on part (a). It is not one.
Precomposing with the map `A(Y) → 𝒪(Y)` gives the same map, and nothing in
either round trip needs it to be injective or surjective. The statement is also
free of the algebraically closed hypothesis, which (a) does need.

The identity carrying the whole proof is `f(ψ(x)) = h(f̄)(x)` for every
polynomial `f`, where `ψ(x)ᵢ = h(x̄ᵢ)(x)`. Both sides are `k`-algebra maps out of
`MvPolynomial σ k` in `f` and agree on the variables, so they agree. Landing in
`Y` and being a morphism both fall out of it: the first because `f̄ = 0` for
`f ∈ I(Y)`, the second by Lemma 3.6, since the coordinates of `ψ` are the values
of `h` and so regular by construction.


## Depends on

- [Morphisms](morphism.md)
- [The ring of regular functions](ring-of-regular-functions.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Proof depends on

- [The coordinate ring is the ring of regular functions](global-regular-eq-coordinate-ring.md)
- [Criterion for a morphism into an affine variety](morphism-to-affine-criterion.md)

## Sources

- [Hartshorne I.3, Proposition 3.5 (p. 19)](../../sources/hartshorne.md#i3)
