---
article_id: af_ff5ac38b7941cc148e224b10
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-6-7]
---

# Pullback on Picard groups

For every scheme morphism `f : X → Y`, prove that module-sheaf pullback sends
invertible sheaves to invertible sheaves and induces a group homomorphism

`f* : Pic Y → Pic X`.

Prove compatibility with identities, composition, tensor products, and duals.
The unique main result is the homomorphism; functoriality is its required API.

## Depends on

- [The Picard group of a ringed space](../cartier-picard/invertible-sheaf-group.md)
- [Pushforward, pullback, and their adjunction](../../modules-and-quasicoherent/module-push-pull-adjunction.md)

## Proof depends on

- `Scheme.Modules.pullback`, `pullbackId`, and `pullbackComp`.
- Pullback of a locally free rank-one module is locally free of rank one.

## Sources

- [Hartshorne II.6, Exercise 6.8(a) on printed p.148](../../../../sources/hartshorne-ii-6.md#adopted-exercises-and-later-use-evidence)
