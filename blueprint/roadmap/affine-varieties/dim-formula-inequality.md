---
article_id: af_dbf6174162e22fb1ef61e8b6
declaration: theorem
origin: background
source_units: [chapter-i-section-1]
statement: formalized
proof: formalized
lean: Hartshorne.ringKrullDim_quotient_eq_coheight Hartshorne.height_add_ringKrullDim_quotient_le
---

# One inequality of the dimension formula

For any commutative ring `R` and any prime `𝔭`,
`height 𝔭 + dim R/𝔭 ≤ dim R`.

This is the direction of Hartshorne's Theorem 1.8A(b) that costs nothing. A
chain of primes below `𝔭` and a chain above it meet at `𝔭` and splice into one
chain, whose length is the sum. No finite generation, no domain, no field.

It is split out because the two directions have nothing in common. This one is
a one-line observation about chains; the reverse is the catenary property, which
is false for general Noetherian rings and is [the open node](dim-formula-catenary.md).

## Depends on

- [Dimension of a topological space and of a ring](dimension.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)
