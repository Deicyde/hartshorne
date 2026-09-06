---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.dim_eq_dim_closure Hartshorne.dim_closure_le_dim Hartshorne.dim_le_dim_closure Hartshorne.inter_eq_inter_isOpen Hartshorne.isIrreducible_inter_of_subset_closure Hartshorne.closure_inter_eq_of_subset_closure Hartshorne.isPreirreducible_preimage_val Hartshorne.isIrreducible_preimage_val Hartshorne.restrictToY Hartshorne.strictMono_restrictToY Hartshorne.zeroLocusOfPrime Hartshorne.zeroLocusOfPrime_subset_closure Hartshorne.mem_zeroLocusOfPrime Hartshorne.zeroLocusOfPrime_lt
---

# Dimension of a quasi-affine variety

If `Y` is a quasi-affine variety then `dim Y = dim Ȳ` (Proposition 1.10).

One inequality is easy: closures of a chain of irreducible closed subsets of `Y`
form a chain in `Ȳ`. For the other, choose a maximal chain in `Y`, note that its
bottom term must be a point `P`, and read the chain in `A(Ȳ)` as primes
contained in the maximal ideal `𝔪_P`. Then `height 𝔪_P = n`, and since
`A(Ȳ)/𝔪_P ≅ k` has dimension `0`, the second half of Theorem 1.8A gives
`n = dim A(Ȳ) = dim Ȳ`.

This is the first proof in the chapter that genuinely needs the additivity
statement `height 𝔭 + dim B/𝔭 = dim B` rather than just the transcendence-degree
statement, which is worth knowing when scheduling the background node.

## Status

Proved, as `Hartshorne.dim_eq_dim_closure`.

The easy inequality (`Hartshorne.dim_le_dim_closure`), for an
arbitrary subset rather than just a quasi-affine variety: a chain of irreducible
closed subsets of a subspace is no longer than one upstairs. Mathlib states that
for an inducing map, and the inclusion of `Y` into its closure is inducing
because both carry the topology induced from the ambient space.

The algebraic input to the reverse inequality is also in place: every maximal
ideal of a finitely generated domain over a field has height the whole dimension
(`Hartshorne.height_eq_ringKrullDim_of_isMaximal`), which is the dimension
formula applied at a maximal ideal.

The two geometric facts the reverse inequality turns on are proved. For `V` an
irreducible closed subset of `Ȳ` meeting `Y`:

- `V ∩ Y` is irreducible (`isIrreducible_inter_of_subset_closure`), because it
  is `V` intersected with an *ambient* open set — the closed half of the locally
  closed presentation `Y = V₀ ∩ U` does nothing, `V` already lying inside `V₀` —
  and a nonempty open piece of an irreducible set is irreducible;
- and `V` is its closure (`closure_inter_eq_of_subset_closure`), so intersecting
  with `Y` loses nothing and is therefore injective and strictly monotone on
  such subsets.

Those two now package into a strictly monotone map
(`Hartshorne.restrictToY`, `Hartshorne.strictMono_restrictToY`)

`{Z irreducible closed in the ambient space | P ∈ Z ⊆ Ȳ} → IrreducibleCloseds ↥Y`,

sending `Z` to its trace on `Y`. Irreducibility of the trace has to be moved
onto the subtype, which needs that the inclusion of a subspace *reflects*
irreducibility — Mathlib has the forward direction along a continuous map but
not this one, so it is proved here from the fact that opens of a subspace are
traces of ambient opens.

Feeding a chain into it is the last step (`Hartshorne.dim_closure_le_dim`).
A prime `𝔭` of `A(Ȳ)` gives the irreducible closed set `Z(𝔭)` cut out by its
preimage in the polynomial ring (`Hartshorne.zeroLocusOfPrime`); that set lies
inside `Ȳ` because the preimage contains `I(Ȳ)`, contains `P` as soon as
`𝔭 ⊆ 𝔪_P`, and the assignment reverses strict inclusions. A chain realising
`height 𝔪_P` therefore becomes, read backwards and restricted to `Y`, a chain in
`IrreducibleCloseds ↥Y` of the same length, so
`dim Ȳ = height 𝔪_P ≤ dim Y`.

Two Lean details are worth recording. The height result is stated for a ring in
the *same* universe as `k`, so the ambient space has to be `Fin m → k` rather
than `σ → k` for a general index type; every other dimension result in the
chapter already carries that restriction. And the chain construction is slow
enough to need a raised heartbeat limit, the cost sitting in the elaboration of
the restricted chain rather than in any one tactic.

## Depends on

- [Dimension of a topological space and of a ring](dimension.md)
- [Affine and quasi-affine varieties](affine-variety.md)

## Proof depends on

- [Dimension is the dimension of the coordinate ring](dim-eq-coordinate-ring-dim.md)
- [Dimension of a finitely generated domain](dim-fg-domain.md)
- [The dimension formula for a finitely generated domain](dim-formula-catenary.md)
- [Algebraic sets and radical ideals](radical-ideal-correspondence.md)

## Sources

- [Hartshorne I.1, Proposition 1.10 (p. 6)](../../sources/hartshorne.md#i1)
