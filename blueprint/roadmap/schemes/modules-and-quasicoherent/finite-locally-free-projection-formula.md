---
article_id: af_72f51b519fff302ff45444ad
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Ringed.projectionFormulaMap Hartshorne.Ringed.projectionFormulaMap_isIso Hartshorne.Ringed.projectionFormulaIso Hartshorne.Ringed.projectionFormulaMap_naturality_left Hartshorne.Ringed.projectionFormulaMap_naturality_right
---

# Projection formula for finite locally free sheaves

For a morphism of ringed spaces $f : X \longrightarrow Y$, an $\mathcal{O} _X$-module $F$, and a
finite locally free $\mathcal{O} _Y$-module $E$, prove the natural isomorphism

$f_*(F \otimes f^* E) \cong f_*F \otimes E$.

Use finite locally free duality and the two adjunctions to show that both sides
represent the same functor.  This is Exercise 5.1(d), later invoked explicitly
in the surface theory.

## Depends on

- [Pushforward, pullback, and their adjunction](module-push-pull-adjunction.md)
- [Tensor products of module sheaves](module-tensor-product.md)

## Proof depends on

- [Duality for finite locally free sheaves](finite-locally-free-duality.md)
- Yoneda identifies two objects from natural isomorphisms of their represented
  Hom functors.

## Sources

- [Hartshorne II.5, Exercise 5.1(d), later used in V](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
