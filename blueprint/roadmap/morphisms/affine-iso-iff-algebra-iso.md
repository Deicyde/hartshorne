---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.nonempty_isIso_iff_nonempty_algEquiv Hartshorne.homToAlgHom_eq_pullback_comp Hartshorne.coordinateRingEquivRegularTop
---

# Isomorphism via coordinate rings

Two affine varieties `X` and `Y` are isomorphic if and only if `A(X)` and `A(Y)`
are isomorphic as `k`-algebras (Corollary 3.7).

Immediate from the bijection of the previous node applied in both directions,
together with the fact that `α` respects composition and identities, so it
carries inverse pairs to inverse pairs.

Making "respects composition" precise is the only work. The map of Proposition
3.5 factors as pullback of regular functions precomposed with `A(Y) ≅ 𝒪(Y)`
(`homToAlgHom_eq_pullback_comp`), and pullback is contravariantly functorial, so
functoriality of the bijection is functoriality of pullback. Forward, that turns
a two-sided inverse pair of morphisms into one of algebras directly. Backward, it
lets the two composites be recognised as identities by comparing their images
under an injective map.

That backward direction is where the definition of isomorphism earns its
awkwardness. Exercise 3.2 shows a bijective bicontinuous morphism need not be an
isomorphism, so what has to be produced is a two-sided *inverse morphism*, and
Proposition 3.5 is what produces one.

Worth stating separately because it is the concrete form the equivalence takes
in practice, and because it is the statement Hartshorne's exercises invoke — for
instance to distinguish the conics `y = x²` and `xy = 1`, whose coordinate rings
are `k[t]` and `k[t, t⁻¹]`.

## Depends on

- [Morphisms into an affine variety](hom-affine-bijection.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)
- [The ring of regular functions](ring-of-regular-functions.md)

## Proof depends on

- [The coordinate ring is the ring of regular functions](global-regular-eq-coordinate-ring.md)

## Sources

- [Hartshorne I.3, Corollary 3.7 (p. 20)](../../sources/hartshorne.md#i3)
