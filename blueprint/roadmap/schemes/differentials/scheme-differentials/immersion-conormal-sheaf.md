---
article_id: af_16b35b95a8072241ce2a54a1
declaration: def
origin: bridged
---

# The conormal sheaf of an immersion

Let `i : Z → X` be an immersion. Use its canonical factorization
`Z → U ↪ X` as a closed immersion `i'` followed by an open immersion. If `I`
is the ideal sheaf of `i'`, define the conormal sheaf `N^*_i` on `Z` to be
`i'^*I`. Expose its canonical identification with `I/I²` after pushforward:

`i'_*N^*_i ≅ I/I²`.

The construction must use the actual ideal sheaf; it may not define the
diagonal conormal sheaf to be the relative differential sheaf.

## Depends on

- [Open immersions and open subschemes](../../subschemes-and-dimension/open-immersions.md)
- [Closed immersions and closed subschemes](../../subschemes-and-dimension/closed-immersions.md)
- [Ideal sheaves of closed immersions](../../coherent-sheaves/closed-immersion-ideal-sheaf.md)
- [Tensor products of module sheaves](../../modules-and-quasicoherent/module-tensor-product.md)

## Proof depends on

- Restriction and quotient compatibility for module sheaves.
- Stacks Project, Section 29.32, tags `01R1`–`01R3`, for the conormal sheaf
  and its `I/I²` description.

## Sources

- [Hartshorne II.8, definition of the differential sheaf as a diagonal conormal sheaf (pp. 175–176)](../../../../sources/hartshorne-ii-8.md#modules-and-sheaves-of-differentials)
- [Adopted Stacks sources for scheme differentials](../../../../sources/hartshorne-ii-8.md#external-proof-sources-and-unresolved-obligations)
