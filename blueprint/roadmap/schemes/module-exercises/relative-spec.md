# Relative Spec of a quasi-coherent algebra

Let $A$ be a quasi-coherent sheaf of $\mathcal{O}_Y$-algebras. There is a unique scheme $X$
and morphism $f : X \to Y$ such that for every open affine $V \subseteq Y$,
$f^{-1}(V) \cong \operatorname{Spec} A(V)$ as schemes over $V$, and for every inclusion $U \hookrightarrow V$ of open
affines of $Y$, the morphism $f^{-1}(U) \to f^{-1}(V)$ corresponds to the restriction
homomorphism $A(V) \to A(U)$. Here uniqueness means up to a unique isomorphism over $Y$
compatible with these identifications. Write $\operatorname{Spec}_Y A$ for this scheme; the
morphism $f$ is affine, and
$f_*\mathcal{O}_{\operatorname{Spec}_Y A} \cong A$. Conversely, every affine morphism is canonically of
this form. These constructions induce mutually inverse bijections between
isomorphism classes of quasi-coherent $\mathcal{O}_Y$-algebras and isomorphism classes
of affine schemes over $Y$. No categorical equivalence is asserted here.

## Depends on

- [The affine-morphism criterion](affine-morphism-criterion.md)
- [Quasi-coherent affine-local criterion](../modules-and-quasicoherent/quasicoherent-affine-local-criterion.md)

## Proof depends on

- [Gluing schemes](../spectrum-and-schemes/gluing.md)
- [Affine change of rings](../modules-and-quasicoherent/affine-tilde/tilde-affine-change-of-rings.md)

## Sources

- [Hartshorne II.5, Exercise 5.17(c,d) (p.128)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
