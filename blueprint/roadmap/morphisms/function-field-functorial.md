---
article_id: af_3bfd873df32de1e7b9c89d8a
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.VarietyHom.functionFieldHom
---

# The function field is functorial for dominant morphisms

A dominant morphism $\varphi:X\to Y$ induces a pullback homomorphism

$$\varphi^*:K(Y)\longrightarrow K(X).$$

Dominance ensures that the inverse image of every nonempty open subset
of $Y$ is nonempty, so pulling back a rational representative is defined.
These maps respect identity and composition, reversing the direction of
morphisms.

An isomorphism of varieties induces an isomorphism of function fields.
The inclusion of a nonempty open subvariety also induces an isomorphism:
restriction is injective by the identity principle, and a rational
representative on the open subvariety is also a representative on an
open subset of the ambient variety.

## Depends on

- [The function field of an arbitrary variety](function-field-abstract.md)
- [Morphisms](morphism.md)

## Proof depends on

- [Varieties](variety.md)
- [Regular functions on a quasi-projective variety](regular-function-quasi-projective.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(c) (pp. 18-19)](../../sources/hartshorne.md#i3)
