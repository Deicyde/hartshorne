---
article_id: af_fba93f17440fd9df524dbffe
declaration: def
origin: cited
mathlib: true
mathlib_declaration: AlgebraicGeometry.Scheme.Hom.fiberHomeo
mathlib_file: Mathlib/AlgebraicGeometry/Fiber.lean
---

# The underlying space of a fiber

The underlying topological space of $X_y$ is homeomorphic to the set-theoretic inverse image $f^{-1}(\{y\})$ with the induced topology.

The map from the fiber to $X$ is a preimmersion. Compute its range as the inverse image of the range of $\operatorname{Spec} \kappa (y) \to Y$, which is the singleton $\{y\}$, and restrict its embedding homeomorphism.

## Depends on

- [The fiber of a morphism](scheme-fiber.md)

## Proof depends on

- The fiber inclusion has image equal to the inverse image of the residue-field point.

## Sources

- [Hartshorne II.3 (fiber-products-fibers-and-base-extension)](../../../sources/hartshorne-ii-3.md#fiber-products-fibers-and-base-extension)
