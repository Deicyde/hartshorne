---
article_id: af_dae717a792f8af7b8c1043d8
declaration: theorem
origin: cited
source_units: [chapter-i-section-4]
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

The Lean target must retain that scope explicitly. The current abstract
`Variety` structure records regular functions and irreducibility, but does not
record that the space came from an affine, quasi-affine, projective, or
quasi-projective construction. Proposition 4.3 is false for an arbitrary
structure with only those fields. Its implementation should therefore package
an affine-open-basis witness (for example `Variety.HasAffineOpenBasis`) and
prove it for the concrete constructors; downstream §4 statements quantify over
varieties carrying that witness.

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
- [The charts are isomorphisms of varieties](../morphisms/projective-rings/chart-isomorphism.md)
- [The vanishing ideal](../affine-varieties/vanishing-ideal.md)
- [Algebraic sets and radical ideals](../affine-varieties/radical-ideal-correspondence.md)

## Sources

- [Hartshorne I.4, Proposition 4.3 (p. 25)](../../sources/hartshorne.md#i4)
