---
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.VarietyHom.ratPullback Hartshorne.VarietyHom.functionFieldHom Hartshorne.VarietyHom.dense_range_of_surjective Hartshorne.VarietyHom.bijective_functionFieldHom_of_isIso Hartshorne.dense_range_inclHom Hartshorne.pushRat Hartshorne.bijective_functionFieldHom_inclHom
---

# The function field is functorial for dominant morphisms

A rational function cannot be pulled back along an arbitrary morphism: the
preimage of a nonempty open set can be empty, and then there is no
representative left. It can be pulled back along a *dominant* one, and dominance
is exactly the condition that makes the preimage nonempty.

One construction then covers both cases Theorem 3.4(c) needs. An isomorphism is
surjective, so its range is dense. The inclusion of a nonempty open subset of an
irreducible space is dense for the same reason the identity principle works. So
`K(Y) ≅ K(X)` along an isomorphism, and `K(Y) ≅ K(Z)` for `Z` open in `Y`, are
two instances of the same map.

## Why this is easier than the germ version

[The germ version](local-ring-functorial.md) had to be stated as bijectivity of
one map rather than as an equation between inverse composites, because the map
induced by the inverse morphism is indexed by `ψ(φ(P))` and not by `P`, and
equating composites would need a rewrite inside the type of a ring hom.

A rational function has no base point. Nothing is indexed by a point, the
transport never arises, and the two statements come out directly. The one new
obligation in each case is nonemptiness of a domain, and irreducibility
discharges it: for injectivity of the open-inclusion map, the triple overlap of
two domains with `Z` is nonempty because a variety is irreducible, where the
germ argument had the point `P` sitting in all three.

Surjectivity in the open-inclusion case reuses the germ machinery unchanged —
the same `pullPoint`, the same regularity transfer — with only the nonemptiness
clause added.

## Depends on

- [The function field of an arbitrary variety](function-field-abstract.md)
- [Morphisms](morphism.md)

## Proof depends on

- [Varieties](variety.md)
- [Regular functions on a quasi-projective variety](regular-function-quasi-projective.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(c) (pp. 18-19)](../../sources/hartshorne.md#i3)
