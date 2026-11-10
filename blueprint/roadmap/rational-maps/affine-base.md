---
article_id: af_dae717a792f8af7b8c1043d8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Variety.hasAffineOpenBasis_ofQuasiProjective Hartshorne.Variety.hasAffineOpenBasis_ofQuasiAffine Hartshorne.Variety.hasAffineOpenBasis_ofProjective
---

# Open affine sets are a base for the topology

For every variety in Hartshorne's four concrete classes, the open subsets that
are affine — isomorphic to an affine variety — form a base for the topology
(Proposition 4.3).

This is the statement that makes "reduce to the affine case" a legitimate move
for an arbitrary variety and not just for a projective one covered by charts.
Every later argument in the section uses it.

The conclusion applies to Hartshorne's concrete varieties. An abstract
irreducible space with regular-function algebras need not have affine
neighbourhoods; an affine-open basis is therefore retained as an explicit
hypothesis in results stated in that more general language.

## The proof

Given $P \in U \subseteq Y$ with $U$ open, a smaller affine open neighbourhood is wanted.
Three reductions and one construction:

- $U$ is itself a variety, so replace $Y$ by $U$ and look for an affine open
  set containing $P$ in $Y$;
- every variety is covered by quasi-affine ones ([Corollary I.2.3](../projective-varieties/affine-cover.md)), so assume $Y$
  is quasi-affine in $\mathbb{A} ^{n}$;
- let $Z=\overline Y\setminus Y$, closed in $\mathbb{A} ^{n}$, with ideal $\mathfrak{a} = I(Z)$. Since $P \notin Z$ and $Z$
  is closed, some $f \in \mathfrak{a}$ has $f(P) \ne 0$.

Then with $H = Z(f)$ the hypersurface: $Z \subseteq H$ and $P \notin H$, so
$P\in Y\setminus(Y\cap H)$, an open subset of $Y$. That set equals $Y\setminus(Y\cap H)$ viewed
inside $\mathbb A^n\setminus H$, where it is *closed*, because everything of $\overline{Y}$ that was
thrown away lies in $Z \subseteq H$. A closed subvariety of an affine variety is
affine, and $\mathbb A^n\setminus H$ is affine by
[Lemma 4.2](hypersurface-complement.md). So $Y\setminus(Y\cap H)$ is the affine
neighbourhood wanted.

The one step that repays attention is why $Y\setminus(Y\cap H)$ is closed in $\mathbb A^n\setminus H$ and
not merely locally closed: $\overline Y\setminus H$ is closed in $\mathbb A^n\setminus H$, and
$Y\setminus(Y\cap H)=\overline Y\setminus H$ exactly because $\overline Y\setminus Y=Z$ is inside $H$.

## Depends on

- [Varieties](../morphisms/variety.md)
- [The complement of a hypersurface is affine](hypersurface-complement.md)

## Proof depends on

- [Varieties are covered by affine pieces](../projective-varieties/affine-cover.md)
- [The charts are isomorphisms of varieties](../morphisms/projective-rings/chart-isomorphism.md)
- [The vanishing ideal](../affine-varieties/vanishing-ideal.md)
- [Algebraic sets and radical ideals](../affine-varieties/radical-ideal-correspondence.md)
- [Every finitely generated domain is a coordinate ring](../affine-varieties/coordinate-ring-realization.md)

## Sources

- [Hartshorne I.4, Proposition 4.3 (p. 25)](../../sources/hartshorne.md#i4)
