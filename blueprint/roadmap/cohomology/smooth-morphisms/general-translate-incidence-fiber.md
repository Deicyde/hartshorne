---
declaration: theorem
origin: bridged
source_units: [chapter-iii-section-10]
---

# Fibres of the general-translate incidence scheme

For maps `f : Y -> X` and `g : Z -> X` as in Kleiman's theorem, form

`W = (G times Y) times_X Z`

using the action-family map, and let `q : W -> G`. For every `sigma : G(k)`,
construct a scheme isomorphism between the fibre
`W_sigma` and `Y^sigma times_X Z`. If the fibre is nonempty, its dimension
under a smooth restriction of `q` is `dim Y + dim Z - dim X`.

Also prove that a regular finite-type fibre has finitely many connected
components. The common dimension of its nonempty components follows from the
equidimensional incidence space and the constant relative dimension of the
smooth restriction of `q`, not from regularity alone.

## Depends on

- [The general-translate incidence space is nonsingular](general-translate-incidence-regular.md)
- [The fibre of a morphism](../../schemes/fiber-products/scheme-fiber.md)
- [Base extension](../../schemes/fiber-products/base-extension.md)
- [Dimension of a scheme](../../schemes/subschemes-and-dimension/scheme-dimension.md)

## Proof depends on

- Pullback pasting and translation isomorphisms.
- A regular Noetherian scheme is locally connected; quasi-compactness then
  gives finitely many connected components.
- Relative dimensions are preserved by base change and add under composition.

## Sources

- [Hartshorne III.10, incidence construction in Theorem 10.8, pp.273–274](../../../sources/hartshorne-iii-10.md#homogeneous-spaces-kleiman-and-bertini-pp272275)
