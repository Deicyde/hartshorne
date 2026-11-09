---
article_id: af_782acfedef3c273801b29df6
declaration: isomorphism
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.veroneseSubring Hartshorne.veronese Hartshorne.Veronese.awayEquiv Hartshorne.Veronese.toProj Hartshorne.Veronese.awayι_comp_toProj Hartshorne.Veronese.projIso Hartshorne.Veronese.twistIso Hartshorne.Veronese.dupleEmbedding Hartshorne.Veronese.isClosedImmersion_dupleEmbedding Hartshorne.Veronese.dupleMapInt Hartshorne.Veronese.dupleMap Hartshorne.Veronese.dupleEmbedding_eq_comp_dupleMap Hartshorne.Veronese.adjoin_dupleCoords Hartshorne.Veronese.isClosedImmersion_dupleMapInt Hartshorne.Veronese.isClosedImmersion_dupleMap
---

# Veronese Proj and twists

Let $S$ be generated in degree one and $S^{(d)}=\bigoplus_n S_{nd}$ for
$d>0$. There is a canonical isomorphism

$\operatorname{Proj} S^{(d)} \cong \operatorname{Proj} S$

under which $\mathcal{O}_{\operatorname{Proj} S^{(d)}}(1)$ corresponds to $\mathcal{O}_{\operatorname{Proj} S}(d)$.

If $x_0,\dots,x_n$ generate $S_1$, giving a closed immersion
$X=\operatorname{Proj} S\to\mathbb{P}^n_{S_0}$, then the monomials of degree
$d$ in the $x_i$ generate $S^{(d)}_1=S_d$. Through the isomorphism above, the
closed immersion of $\operatorname{Proj} S^{(d)}$ into $\mathbb{P}^N_{S_0}$
that they define ($N+1$ being the number of these monomials) is
$X\to\mathbb{P}^n_{S_0}$ followed by the $d$-uple embedding of
$\mathbb{P}^n_{S_0}$, the morphism $\mathbb{P}^n_{S_0}\to\mathbb{P}^N_{S_0}$
given by all monomials of degree $d$ in the homogeneous coordinates.

## Depends on

- [Twisting sheaves are invertible](proj-twisting-sheaf.md)
- [Degree-one-generated Proj is projective](../proper-and-projective/generated-proj-projective.md)

## Proof depends on

- [A standard Proj chart is affine](../projective-spectrum/proj-basic-open.md)
- The degree-$d$ monomial description of the Veronese embedding from
  Hartshorne I, Exercise 2.12.
- The canonical chartwise identification of $\operatorname{Proj} S^{(d)}$ with $\operatorname{Proj} S$.

## Sources

- [Hartshorne II.5, Exercise 5.13 (p.126)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
