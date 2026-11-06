---
article_id: af_adc120ac77975fd8f65f1adc
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.varietyAssociatedScheme Hartshorne.varietyAssociatedScheme_toSheafedSpace Hartshorne.varietyAssociatedScheme_presheaf Hartshorne.genericCompletionSheafedSpace Hartshorne.SchemeVarietyCat.toScheme
---

# A variety with an affine-open basis has an associated scheme

For a variety $V$ with an affine-open basis, the ringed space
$(t(V),\alpha_{V*}\mathcal{O}_V)$ is a scheme.

As throughout Chapter I, the base field $k$ is algebraically closed; the
affine comparison rests on the Nullstellensatz.

Given a point of $t(V)$, choose a classical point in its nonempty irreducible
closed subset and then an affine open neighbourhood of that point in $V$.
The corresponding open in $t(V)$ is affine by the affine comparison.  This
establishes the required local affineness.

In more detail, if $g : W \to V$ is an open embedding of varieties along which
every regular function on an open subset of $W$ descends to its image, then
$Z \mapsto \overline{g(Z)}$ together with pullback of regular functions is an
open immersion $(t(W),\alpha_{W*}\mathcal{O}_W) \to (t(V),\alpha_{V*}\mathcal{O}_V)$
whose image consists of the irreducible closed subsets meeting $g(W)$: such a
$Z'$ is the closure of $Z' \cap g(W)$, a nonempty open subset of $Z'$.  Applied
to an affine open neighbourhood $U \cong Y$, this realizes $\operatorname{Spec} A(Y)$
as an open subspace of $t(V)$ containing the given point.  In particular the
stalks of $\alpha_{V*}\mathcal{O}_V$ are local rings.

## Depends on

- [The scheme-variety source category](scheme-variety-category.md)
- [An affine variety completes to its spectrum](affine-variety-to-spec.md)
- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Sources

- [Hartshorne II.2, passage from the affine case to arbitrary varieties in Proposition 2.6 (p. 78)](../../../sources/hartshorne-ii-2.md#schemes-over-a-base-and-proposition-26)
