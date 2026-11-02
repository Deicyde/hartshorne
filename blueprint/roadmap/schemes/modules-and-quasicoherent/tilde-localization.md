---
article_id: af_e50bd55d0e4eeadcb033ff3f
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.affineTildeBasicOpenIso
---

# The affine tilde sheaf and localization

For a ring $A$ and an $A$-module $M$, construct the $\mathcal{O} _{\operatorname{Spec} A}$-module
$\widetilde{M}$ whose local sections are locally fractions.  The canonical maps exhibit

- $\Gamma (D(f), \widetilde{M})$ as the localization $M_f$;
- the stalk $\widetilde{M}_{\mathfrak{p}}$ as the localization $M_{\mathfrak{p}}$; and
- $\Gamma (\operatorname{Spec} A,\widetilde{M})$ as $M$.

These localization descriptions are Hartshorne's Proposition II.5.1.

## Depends on

- [Sheaves of modules](sheaves-of-modules.md)
- [The stalk of Spec](../spectrum-and-schemes/spec-stalk.md)
- [Sections on a principal open](../spectrum-and-schemes/spec-basic-open-sections.md)
- [Global sections of an affine spectrum](../spectrum-and-schemes/spec-global-sections.md)

## Proof depends on

- Localization of a module at a prime and away from one element.
- Principal opens form a basis of $\operatorname{Spec} A$.

## Sources

- [Hartshorne II.5, Proposition 5.1 on printed p. 110](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
