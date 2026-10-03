---
declaration: theorem
origin: cited
source_units: [chapter-ii-section-5]
---

# Pushforward under Hartshorne's finiteness hypotheses

Let `f : X ⟶ Y` be a scheme morphism.  Assume either that `X` is Noetherian,
or that `f` is quasi-compact and separated.  Then `f_*` sends quasi-coherent
`O_X`-modules to quasi-coherent `O_Y`-modules.

Over an affine open of `Y`, choose a finite affine cover of its inverse image
and finite affine covers of all pairwise intersections.  Express `f_*F` as the
kernel of the difference map between finite sums of affine pushforwards and
apply abelian closure of quasi-coherent modules.

## Depends on

- [Pushforward, pullback, and their adjunction](module-push-pull-adjunction.md)
- [Quasi-coherence by local presentations](quasicoherent-local-presentations.md)
- [Quasi-compact morphisms](../first-properties/quasi-compact-morphism.md)
- [Noetherian schemes and finite affine covers](../first-properties/noetherian-scheme.md)
- [Separated morphisms](../separated-morphisms/separated-morphism.md)

## Proof depends on

- [Abelian closure of quasi-coherent sheaves](quasicoherent-abelian-closure.md)
- [Tilde under affine change of rings](tilde-affine-change-of-rings.md)
- [Affine intersections in a separated scheme](../separated-morphisms/separated-affine-intersection.md),
  for Hartshorne's separated special case.
- [Noetherian spaces and quasi-compact opens](../foundational-properties/noetherian-space-open-compact.md),
  for Hartshorne's Noetherian-source special case.
- In a Noetherian space all open subsets, including affine-cover overlaps,
  are quasi-compact.

## Sources

- [Hartshorne II.5, Proposition 5.8(c) on printed p. 115](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
