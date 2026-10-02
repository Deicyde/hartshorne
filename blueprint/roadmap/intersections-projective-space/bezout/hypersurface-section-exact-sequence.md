---
article_id: af_d1b9ce8ff30814a78d9c8131
declaration: theorem
origin: bridged
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.hypersurfaceSection_degreewise_exact_int
---

# The hypersurface-section coordinate-ring sequence is exact

Assume `n > 0`. Let `Y ⊆ ℙⁿ` be a projective variety, let `f` be an
irreducible homogeneous polynomial of positive degree `d`, and put
`H = Z(f)`. If `Y` is not contained in `H`, multiplication by `f` and the
quotient map give the graded short exact sequence

`0 → S(Y)(-d) → S(Y) → S/(J(Y) + J(H)) → 0`.

Equivalently, in every integer degree `l`, multiplication by `f` is
injective, its range is the kernel of the quotient map, and that quotient map
is surjective. The last module is deliberately nonreduced: it is the module
used for hypersurface intersection multiplicities, not generally the reduced
coordinate ring of `Y ∩ H`.

The proof uses that `J(H) = (f)` and that `S(Y)` is a domain. Noncontainment
is exactly the assertion that the class of `f` in `S(Y)` is nonzero, so
multiplication is injective. Homogeneous-component extraction supplies a
preimage in the shifted degree for kernel elements, including the negative
and low-degree cases.

## Depends on

- [Integer-graded module twists](../hilbert/graded-module-twists.md)
- [Integer-graded submodules and quotients](../hilbert/graded-submodules-and-quotients.md)
- [Hilbert polynomials and degrees of projective algebraic sets](../hilbert/projective-hilbert-polynomial-and-degree.md)
- [A degree-d hypersurface has degree d](hypersurface-hilbert-polynomial.md)

## Proof depends on

- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)
- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)
- [The homogeneous prime at a point](../../morphisms/projective-rings/point-ideal.md)

## Sources

- [Hartshorne I.7, proof of Theorem 7.7 (p. 53)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
