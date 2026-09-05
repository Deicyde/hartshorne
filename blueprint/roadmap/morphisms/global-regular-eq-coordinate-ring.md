---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.coordinateToRegular Hartshorne.coordinateToRegular_injective Hartshorne.denominators Hartshorne.exists_mem_denominators_evalAt_ne_zero Hartshorne.denominators_eq_top Hartshorne.coordinateToRegular_surjective Hartshorne.coordinateRingEquivGlobalRegular
---

# The coordinate ring is the ring of regular functions

For an affine variety `Y`, the map `α : A(Y) → 𝒪(Y)` sending a polynomial class
to the function it defines is an isomorphism of `k`-algebras (Theorem 3.2(a)).

This is the part of Theorem 3.2 the rest of §3 actually consumes: Proposition
3.5 is stated as a bijection `Hom(X, Y) ≅ Hom_{k-alg}(A(Y), 𝒪(X))`, and it is
`α` that lets the two sides be compared at all.

Injectivity is the correspondence of §1 pushed through the quotient: a
polynomial defining the zero function on `Y` lies in `I(Y)`.

## Surjectivity, by a different route than Hartshorne's

Hartshorne derives surjectivity from part (c), writing
`𝒪(Y) = ⋂_P 𝒪_P = ⋂_𝔪 A(Y)_𝔪 = A(Y)` inside `K(Y)`. That needs the local rings,
their identification with localisations of `A(Y)`, and one fact he takes from
outside: that a domain is the intersection of its localisations at all maximal
ideals.

None of it is needed. Given a regular `f`, take the *ideal of denominators*

`𝔞 = {a ∈ A(Y) : a·f is again a polynomial function}`.

Regularity at `P` writes `f = g/h` near `P` with `h(P) ≠ 0`. Then `h·f` and `g`
are both regular on all of `Y` and agree on that neighbourhood, so the identity
principle makes them agree everywhere: `h̄ ∈ 𝔞`, and `h̄ ∉ 𝔪_P`. So `𝔞` lies in no
maximal ideal, since every maximal ideal is some `𝔪_P` by part (b), and hence
`𝔞 = A(Y)`. Then `1 ∈ 𝔞`, which says exactly that `f` is a polynomial function.

The two ingredients, the identity principle and part (b), were already
available, so this node costs nothing beyond assembling them. It also breaks the
dependency of (a) on (c), which was the reason (a) had been sitting behind the
still-open dimension clause.

Irreducibility of `Y` enters exactly once, to make the identity principle
available.

## Depends on

- [The ring of regular functions](ring-of-regular-functions.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Proof depends on

- [Points and maximal ideals](points-eq-maximal-ideals.md)
- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, Theorem 3.2(a) (p. 17)](../../sources/hartshorne.md#i3)
