---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.IsProjVariety Hartshorne.IsQuasiProjVariety Hartshorne.projDim Hartshorne.IsQuasiProjVariety.isIrreducible Hartshorne.homogeneousVanishingIdeal_univ Hartshorne.isIrreducible_univ_projectiveSpace Hartshorne.isProjVariety_univ
---

# Projective and quasi-projective varieties

A *projective variety* is an irreducible algebraic set in `ℙⁿ` with its induced
topology; a *quasi-projective variety* is a nonempty open subset of one. The
dimension of either is its dimension as a topological space.

The definitions are verbatim the affine ones with `ℙⁿ` in place of `𝔸ⁿ`, so the
node is short. It exists as a separate article because §3 takes the union of the
four kinds of variety — affine, quasi-affine, projective, quasi-projective — as
its objects, and because the dimension results at the end of this chapter are
stated about these types.

## Projective space is itself a variety

`ℙⁿ` is irreducible, the projective form of Example 1.4.1, so it is a projective
variety. That is not automatic from the definition and it is needed the moment
`ℙⁿ` is treated as a variety rather than as an ambient space — Proposition 3.3
does exactly that when it calls the standard charts isomorphisms of varieties.

The affine statement comes from `I(𝔸ⁿ) = 0`; this is the same computation with
one extra step, since a polynomial is not a function on `ℙⁿ`. A homogeneous `f`
vanishing at every point vanishes at every nonzero vector, because the vanishing
criterion may be tested at any representative, and then at `0` as well:
`0 = 0 • w` for a nonzero `w`, and homogeneity turns that into `0ⁿ · f(w)`,
which is `0` uniformly in `n`, degree zero included.

## Depends on

- [The Zariski topology on projective space](projective-zariski-topology.md)
- [Dimension of a topological space and of a ring](../affine-varieties/dimension.md)

## Sources

- [Hartshorne I.2, definitions of projective and quasi-projective variety (p. 10)](../../sources/hartshorne.md#i2)
