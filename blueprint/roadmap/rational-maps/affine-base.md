---
declaration: theorem
origin: cited
---

# Open affine sets are a base for the topology

On any variety `Y`, the open subsets that are affine — isomorphic to an affine
variety — form a base for the topology (Proposition 4.3).

This is the statement that makes "reduce to the affine case" a legitimate move
for an arbitrary variety and not just for a projective one covered by charts.
Every later argument in the section uses it.

## The proof

Given `P ∈ U ⊆ Y` with `U` open, a smaller affine open neighbourhood is wanted.
Three reductions and one construction:

- `U` is itself a variety, so replace `Y` by `U` and look for an affine open
  set containing `P` in `Y`;
- every variety is covered by quasi-affine ones (Corollary 2.3), so assume `Y`
  is quasi-affine in `𝔸ⁿ`;
- let `Z = Ȳ − Y`, closed in `𝔸ⁿ`, with ideal `𝔞 = I(Z)`. Since `P ∉ Z` and `Z`
  is closed, some `f ∈ 𝔞` has `f(P) ≠ 0`.

Then with `H = Z(f)` the hypersurface: `Z ⊆ H` and `P ∉ H`, so
`P ∈ Y − Y ∩ H`, an open subset of `Y`. That set equals `Y − Y ∩ H` viewed
inside `𝔸ⁿ − H`, where it is *closed*, because everything of `Ȳ` that was
thrown away lies in `Z ⊆ H`. A closed subvariety of an affine variety is
affine, and `𝔸ⁿ − H` is affine by
[Lemma 4.2](hypersurface-complement.md). So `Y − Y ∩ H` is the affine
neighbourhood wanted.

The one step that repays attention is why `Y − Y ∩ H` is closed in `𝔸ⁿ − H` and
not merely locally closed: `Ȳ − H` is closed in `𝔸ⁿ − H`, and
`Y − Y ∩ H = Ȳ − H` exactly because `Ȳ − Y = Z` is inside `H`.

## Depends on

- [Varieties](../morphisms/variety.md)
- [The complement of a hypersurface is affine](hypersurface-complement.md)

## Proof depends on

- [Varieties are covered by affine pieces](../projective-varieties/affine-cover.md)
- [The vanishing ideal](../affine-varieties/vanishing-ideal.md)
- [Algebraic sets and radical ideals](../affine-varieties/radical-ideal-correspondence.md)

## Sources

- [Hartshorne I.4, Proposition 4.3 (p. 25)](../../sources/hartshorne.md#i4)
