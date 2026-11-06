---
article_id: af_673f278244a32c7f7febc7e0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.relativeDifferentials_transitivity_exact AlgebraicGeometry.Scheme.pullbackRelativeDifferentialsToComp AlgebraicGeometry.Scheme.relativeDifferentialsCompToLeft AlgebraicGeometry.Scheme.relativeDifferentialsTransitivityIsColimit AlgebraicGeometry.Scheme.pullbackRelativeDifferentialsToComp_unit_d AlgebraicGeometry.Scheme.relativeDifferentialsCompToLeft_d AlgebraicGeometry.Scheme.relativeDifferentialsCompToLeft_spec AlgebraicGeometry.Scheme.pullbackRelativeDifferentialsToComp_spec
---

# The transitivity sequence for differential sheaves

For scheme morphisms $X \to Y \to Z$, construct the natural right-exact sequence
of $\mathcal{O} _X$-modules

$f^* \Omega_{Y/Z} \to \Omega_{X/Z} \to \Omega_{X/Y} \to 0$.

The maps must agree on affine charts with the first exact sequence for
Kähler differentials.

## Depends on

- [The relative differential sheaf](relative-differentials.md)
- [Differentials on affine schemes](affine-relative-differentials.md)
- [The first exact sequence](../kaehler-differentials/kahler-first-exact-sequence.md)
- [Pushforward, pullback, and their adjunction](../../modules-and-quasicoherent/module-push-pull-adjunction.md)

## Proof depends on

- Stalkwise exactness of sheaves of modules.

## Sources

- [Hartshorne II.8, Proposition 8.11, printed p. 176](../../../../sources/hartshorne-ii-8.md)
