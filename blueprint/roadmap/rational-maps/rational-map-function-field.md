---
article_id: af_efc666120dfb5881de675ab4
declaration: theorem
origin: cited
source_units: [chapter-i-section-4]
statement: formalized
proof: formalized
lean: Hartshorne.RationalMapFunctionField.bijective_functionFieldAlgHom_of_hasAffineOpenBasis Hartshorne.RationalMapFunctionField.functionFieldFunctor_isEquivalence
---

# Rational maps and function fields

For varieties `X` and `Y` in Hartshorne's four concrete classes — represented
in Lean together with the affine-open-basis witness of Proposition 4.3 — there
is a bijection between

- dominant rational maps `X ⇢ Y`, and
- `k`-algebra homomorphisms `K(Y) → K(X)`,

and this correspondence is an arrow-reversing equivalence between the category
of such varieties with dominant rational maps and the category of finitely
generated field extensions of `k` (Theorem 4.4).

This is the section's main result and the birational counterpart of Corollary
3.8. There, the coordinate ring determined an affine variety up to isomorphism;
here, the function field determines *any* variety up to birational equivalence.

## The map in one direction

Given a dominant `φ` represented by `⟨U, φ_U⟩` and a rational function on `Y`
represented by `⟨V, f⟩`, dominance makes `φ_U(U)` dense in `Y`, so `φ_U⁻¹(V)` is
a nonempty open subset of `X` and `f ∘ φ_U` is regular on it. That is a rational
function on `X`, and the assignment is a `k`-algebra homomorphism
`K(Y) → K(X)`.

## The inverse

Given `θ : K(Y) → K(X)`, a dominant rational map is built back. By
[Proposition 4.3](affine-base.md) `Y` is covered by affine open sets and
`K(Y) = K(V)` for any of them, so `Y` may be assumed affine. Take generators
`y₁,…,y_n` of `A(Y)` as a `k`-algebra. Their images `θ(yᵢ)` are rational
functions on `X`, so all are regular on some common nonempty open `U ⊆ X`, and
`θ` restricts to an injective `k`-algebra map `A(Y) → 𝒪(U)`. Proposition 3.5
turns that into a morphism `U → Y`, hence a rational map `X ⇢ Y`, and injectivity
of `θ` makes it dominant. The two constructions are mutually inverse.

## Why the categories match up

Two closure statements finish the equivalence. Every `K(Y)` is a finitely
generated field extension of `k`: pass to an affine open subset, where Theorem
3.2(d) identifies `K(Y)` with the fraction field of `A(Y)`. Conversely every
finitely generated `K/k` is some `K(Y)`: take generators `y₁,…,y_n ∈ K`, let `B`
be the `k`-subalgebra they generate, note `B` is a quotient of a polynomial ring
and a domain, so `B ≅ A(Y)` for a variety `Y` in `𝔸ⁿ` by the realization
half of Corollary 3.8, and then `K ≅ K(Y)`.

## Depends on

- [Composition of dominant rational maps](rational-map-composition.md)
- [The function field of an arbitrary variety](../morphisms/function-field-abstract.md)
- [Open affine sets are a base for the topology](affine-base.md)

## Proof depends on

- [Morphisms into an affine variety](../morphisms/hom-affine-bijection.md)
- [The function field is functorial for dominant morphisms](../morphisms/function-field-functorial.md)
- [The function field is the fraction field](../morphisms/function-field-is-fraction-field.md)
- [Equivalence with finitely generated domains](../morphisms/affine-variety-equivalence.md)
- [The coordinate ring is the ring of regular functions](../morphisms/global-regular-eq-coordinate-ring.md)
- [Global regular functions are the intersection of the local rings](../morphisms/global-functions/global-regular-intersection-local-rings.md)

## Sources

- [Hartshorne I.4, Theorem 4.4 (pp. 25-26)](../../sources/hartshorne.md#i4)
