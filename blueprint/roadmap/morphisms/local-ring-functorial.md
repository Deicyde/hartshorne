---
article_id: af_59bf5c5a065cb7280464d06c
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.VarietyHom.localRingHom
---

# The local ring is functorial

A morphism $\varphi:X\to Y$ induces a contravariant ring map

$$\mathcal O_{\varphi(P),Y}\longrightarrow\mathcal O_{P,X}.$$

This is Hartshorne's Exercise I.3.3(a). The map pulls back representatives
of germs. It respects identity and composition.

An isomorphism of varieties induces an isomorphism of the corresponding
local rings. The inclusion of an open subvariety also induces an isomorphism
at each of its points. Injectivity follows from the identity principle,
and surjectivity follows because an open neighbourhood inside the open
subvariety is also open in the ambient variety.

## Depends on

- [The local ring at a point](local-ring.md)
- [Morphisms](morphism.md)

## Proof depends on

- [Varieties](variety.md)
- [Regular functions on a quasi-projective variety](regular-function-quasi-projective.md)

## Sources

- [Hartshorne I.3, Exercise 3.3(a) (p. 21)](../../sources/hartshorne.md#i3)
- [Hartshorne I.3, Theorem 3.4(b) (pp. 18-19)](../../sources/hartshorne.md#i3)
