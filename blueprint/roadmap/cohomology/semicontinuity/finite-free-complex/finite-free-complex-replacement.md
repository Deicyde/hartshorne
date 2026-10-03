---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Replacing a bounded-above complex by finite free modules

Let `A` be Noetherian and let `C` be a bounded-above cochain complex of
`A`-modules whose cohomology modules `H^i(C)` are finitely generated. There is
a bounded-above complex `L` of finitely generated free `A`-modules and a
cochain map `L -> C` inducing an isomorphism on every cohomology module.

If every term of `C` is flat over `A`, then for every `A`-module `M` the map

`H^i(L tensor_A M) -> H^i(C tensor_A M)`

is an isomorphism for every `i`.

## Depends on

- [Complexes in an abelian category](../../derived-functors/abelian-complexes-and-homotopy.md)
- [Flat modules in short exact sequences](../../flat-families/flatness/flat-modules-short-exact-calculus.md)

## Proof depends on

- Descending construction of `L^i` from finite generators of `H^i(C)` and of
  the inverse image of the boundary module in `L^(i+1)`.
- The tensor-compatible conclusion follows by descending induction, finite
  free presentations, the five lemma, and exactness of filtered colimits of
  modules.

## Sources

- [Hartshorne III.12, Lemma 12.3, pp.283–284](../../../../sources/hartshorne-iii-11-12.md#cohomology-after-tensor-and-finite-free-models-pp281287)
