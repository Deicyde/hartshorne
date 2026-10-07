## README.md

### Mathlib boundary

The pinned Mathlib exactly proves both clauses of Theorem 6.1A as
`LocalSubring.isMax_iff` and `LocalSubring.exists_le_valuationSubring`.
Its `IsDiscreteValuationRing.TFAE` contains most of Theorem 6.2A, but not the
source's exact four-way statement involving `IsRegularLocalRing` under an
explicit dimension-one hypothesis, so that theorem remains a small project
wrapper.

Open Mathlib PR
[#43655](https://github.com/leanprover-community/mathlib4/pull/43655) develops
discreteness for equivalent valuations and may later simplify the valuation-
subring packaging. Open PRs #28683 and #29574 overlap the missing generic fact
that a regular local ring is a domain. The roadmap targets only the pinned
checkout and does not assume any of these PRs merge.
