---
article_id: af_ed72e66c33713fdbffbf3101
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.relativeDifferentials_isQuasicoherent AlgebraicGeometry.Scheme.relativeDifferentials_isCoherent AlgebraicGeometry.Scheme.relativeDifferentials_isCoherent_of_locallyOfFiniteType
---

# Quasi-coherence and coherence of differentials

For every scheme morphism $f : X \to Y$, the relative differential sheaf
$\Omega_{X/Y}$ is quasi-coherent.  If $Y$ is Noetherian and $f$ is of finite type,
then $\Omega_{X/Y}$ is coherent.

Both statements are local: if $U \subseteq X$ and $V \subseteq Y$ are open with
$f(U) \subseteq V$, then $\Omega_{X/Y}|_U \cong \Omega_{U/V}$, so on affine opens
$U = \operatorname{Spec} B$ over $V = \operatorname{Spec} A$ one has
$\Omega_{X/Y}|_U \cong \widetilde{\Omega_{B/A}}$, and such opens cover $X$.  The coherent
conclusion uses that the affine Kähler modules $\Omega_{B/A}$ are finitely generated when $f$
is locally of finite type.  For coherence in the sense of a cover by affine opens on which the
sheaf comes from finitely generated modules, this already suffices, so the Noetherian hypothesis
on $Y$ is kept only as the setting in which Hartshorne states the result (where $X$ is then
Noetherian and coherence is well behaved).

## Depends on

- [Differentials on affine schemes](affine-relative-differentials.md)
- [The affine-local criterion for quasi-coherence](../../modules-and-quasicoherent/quasicoherent-affine-local-criterion.md)
- [The affine-local criterion for coherence](../../modules-and-quasicoherent/coherent-affine-local-criterion.md)
- [Finiteness of differentials](../kaehler-differentials/finite-type-differentials-finite.md)
- [Finite type over a Noetherian scheme](../../first-properties/finite-type-over-noetherian.md)

## Sources

- [Hartshorne II.8, Remark 8.9.1, printed p. 175](../../../../sources/hartshorne-ii-8.md)
