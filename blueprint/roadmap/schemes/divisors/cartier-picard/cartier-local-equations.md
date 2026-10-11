---
article_id: af_0bc2c79acfbc5253536624b0
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-6-7]
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.toCartierDivisorSheaf_apply_eq_iff_ratio AlgebraicGeometry.Scheme.CartierLocalEquations AlgebraicGeometry.Scheme.CartierLocalEquations.Represents AlgebraicGeometry.Scheme.CartierLocalEquations.existsUnique_represents AlgebraicGeometry.Scheme.CartierLocalEquations.exists_localEquations AlgebraicGeometry.Scheme.CartierLocalEquations.Refines AlgebraicGeometry.Scheme.CartierLocalEquations.SameDivisor AlgebraicGeometry.Scheme.CartierLocalEquations.HaveCommonRefinement AlgebraicGeometry.Scheme.CartierLocalEquations.sameDivisor_iff_commonRefinement
---

# Local equations for Cartier divisors

A global section of `K_X^* / O_X^*` is equivalently represented by an open
cover `U_i` and local equations `f_i ∈ K_X^*(U_i)` whose ratios `f_i/f_j` on
the full overlaps `U_i ∩ U_j` come from regular units.

Every Cartier divisor admits such local equations, and compatible local
equations glue to a unique divisor. Two presentations represent the same
divisor exactly when they admit a common refinement on which their equations
differ by regular units.

## Depends on

- [The Cartier divisor group](cartier-divisor-group.md)

## Proof depends on

- [Quotient sheaves and their stalks](../../sheaves/quotient-sheaf-stalks.md)
- Global sections of a quotient sheaf lift locally on an open cover.
- Exactness of the additive-sheaf cokernel gives a regular unit on each full
  overlap, rather than only after a further refinement.

## Sources

- [Hartshorne II.6, local equations for Cartier divisors on printed p.141](../../../../sources/hartshorne-ii-6.md#cartier-divisors-and-invertible-sheaves)
