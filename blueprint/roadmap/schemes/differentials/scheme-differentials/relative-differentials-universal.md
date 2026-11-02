---
article_id: af_06e9acaca163bf53920d3e2e
declaration: theorem
origin: bridged
lean: AlgebraicGeometry.Scheme.relativeDifferentials_universal
statement: formalized
proof: formalized
---

# The universal property of the relative differential sheaf

For a scheme morphism $f : X \to Y$ and an $\mathcal{O} _X$-module $M$, composition with
the canonical derivation gives a natural equivalence between
$\mathcal{O} _X$-linear morphisms

$\Omega_{X/Y} \to M$

and derivations $\mathcal{O} _X \to M$ that vanish on the image of
$f^{-1}\mathcal{O} _Y \to \mathcal{O} _X$. This equivalence is natural in $M$ and uniquely characterizes
the relative differential sheaf together with its derivation.

## Depends on

- [The relative differential sheaf](relative-differentials.md)
- [Pushforward, pullback, and their adjunction](../../modules-and-quasicoherent/module-push-pull-adjunction.md)

## Proof depends on

- The sheafification adjunction and the universal property of relative presheaf differentials.

## Sources

- [Hartshorne II.8, differential modules and the scheme differential sheaf (pp. 172–176)](../../../../sources/hartshorne-ii-8.md#modules-and-sheaves-of-differentials)
