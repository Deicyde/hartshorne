---
article_id: af_9d9ddee15270ff39e2460179
declaration: def
origin: cited
source_units: [chapter-i-section-6-abstract-curves]
---

# Regular functions on the valuation space

Let `U` be an open subset of the valuation space `C_K`.  Define the algebra of
rational functions regular on `U` by

`𝒪_K(U) = ⋂_{R ∈ U} R ⊆ K`.

For `f ∈ 𝒪_K(U)`, evaluate its residue at every `R ∈ U` to obtain a
function `U → k`.  Define the regular functions on `U` to be the image of
this evaluation map, as a `k`-subalgebra of `U → k`.

On every nonempty open `U`, the evaluation map is injective.  Indeed, if two
rational functions have equal residues, their difference lies in `𝔪_R` for
every `R ∈ U`; the finite-zero form of Lemma 6.5 and infinitude of a
nonempty cofinite open force that difference to be zero.

Keep both the intersection subalgebra inside `K` and its faithful image inside
the function algebra.  Later proofs use the former for field arithmetic and
the latter for the `Variety.regular` field.

For the empty open, the intersection inside `K` is the top subalgebra and the
evaluation map lands in the unique function `∅ → k`; its image is therefore
the full function algebra. Do not assert injectivity in this case. The
injectivity statement, and every later choice of a rational representative,
is restricted to nonempty opens.

## Depends on

- [The cofinite valuation space](valuation-space-topology.md)
- [Residue fields of function-field DVRs](valuation-residue-field.md)

## Proof depends on

- [A rational function has finitely many poles](finite-poles.md)

## Sources

- [Hartshorne I.6, regular functions on open subsets of `C_K` (p. 42)](../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
