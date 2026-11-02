---
article_id: af_02eeba4ecfe5ba1090a09b26
declaration: abbrev
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projectiveSpaceOverScheme Hartshorne.projectiveSpaceOverSchemeProjection
---

# Projective space over a scheme

For a scheme $Y$, define relative projective $n$-space by

$\mathbb{P}^n_Y=\mathbb{P}^n_{\mathbb{Z}}\times_{\operatorname{Spec}\mathbb{Z}}Y$,

with structure morphism the second projection. Expose the canonical base-change
isomorphism

$\mathbb{P} ^{n}_Y \times [Y] Y' \cong \mathbb{P} ^{n}_{Y'}$

and its compatibility with projections. Use the existing scheme projective
space over a ring for $\mathbb{P} ^{n}_{\mathbb{Z}}$; keep this construction distinct from the
project's Chapter-I type of classical projective points.

## Depends on

- [Projective space over a ring](../projective-spectrum/projective-space-over-ring.md)
- [The spectrum of the integers is terminal](../foundational-properties/spec-z-terminal.md)
- [Base extension](../fiber-products/base-extension.md)

## Proof depends on

- [Transitivity of base extension](../fiber-products/base-extension-transitive.md)
- Associativity and symmetry isomorphisms for categorical pullbacks.

## Sources

- [Hartshorne II.4 (projective-morphisms)](../../../sources/hartshorne-ii-4.md#projective-morphisms)
