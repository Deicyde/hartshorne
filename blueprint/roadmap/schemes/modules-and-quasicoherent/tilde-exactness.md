---
article_id: af_b06308387f9e806b6f0b1f2e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.affineTilde_exact Hartshorne.affineTilde_preservesFiniteLimits Hartshorne.affineTilde_map_mono
---

# Exactness of the tilde functor

For every exact sequence of `A`-modules, applying `M ↦ M̃` gives an exact
sequence of `𝒪_{Spec A}`-modules.  Thus the tilde functor preserves kernels,
images, cokernels, and short exact sequences.

This is the exactness clause of Proposition 5.2(a).

## Depends on

- [The affine tilde sheaf and localization](tilde-localization.md)

## Proof depends on

- [Exactness is detected on stalks](../sheaves/stalkwise-exactness.md)
- Localization is an exact functor on modules.

## Sources

- [Hartshorne II.5, Proposition 5.2(a) on printed pp. 110–111](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
