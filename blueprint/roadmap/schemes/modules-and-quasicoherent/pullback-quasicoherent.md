---
article_id: af_406823956960a3ab123d308a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isQuasicoherent_pullback Hartshorne.isCoherent_pullback
---

# Pullback preserves quasi-coherence

For every scheme morphism $f : X \longrightarrow Y$, pullback sends quasi-coherent
$\mathcal{O} _Y$-modules to quasi-coherent $\mathcal{O} _X$-modules.  If $X$ and $Y$ are
noetherian, it sends coherent modules to coherent modules.

This is Proposition 5.8(a,b). The noetherian hypothesis in (b) is Hartshorne's; the argument
below does not use it, and the coherence statement holds for every morphism $f$.  Reduce locally to a morphism of affine schemes,
where pullback is extension of scalars and finite presentation is preserved by
base change.

## Depends on

- [Pushforward, pullback, and their adjunction](module-push-pull-adjunction.md)
- [Quasi-coherence by local presentations](quasicoherent-local-presentations.md)
- [The affine-local criterion for coherence](coherent-affine-local-criterion.md)

## Proof depends on

- [Tilde under affine change of rings](affine-tilde/tilde-affine-change-of-rings.md)
- [The affine-local criterion for quasi-coherence](quasicoherent-affine-local-criterion.md)
- Every point of the source has an affine neighborhood mapping into an affine
  neighborhood of its image.
- Tensoring a finite presentation along a ring homomorphism gives a finite
  presentation.

## Sources

- [Hartshorne II.5, Proposition 5.8(a,b) on printed p. 115](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
