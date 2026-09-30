---
article_id: af_6ab332f43691470db2219d1f
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
---

# Affine products are varieties

For finite coordinate types `σ` and `τ`, define `affineProduct X Y` inside
affine space on `σ ⊕ τ` by requiring its two coordinate restrictions to lie in
`X` and `Y`.  If `X` and `Y` are affine varieties over an algebraically closed
field, then `affineProduct X Y` is an affine variety.  The sole main
declaration is planned as `Hartshorne.isAffineVariety_affineProduct`.

This is Exercise I.3.15(a), adopted because Proposition 7.1 applies it to
`Y × Z ⊆ 𝔸²ⁿ`.  The topology is the one induced from affine space, not the
ordinary product topology.

The closed-set part comes from extending the equations of each factor to the
disjoint union of their variables.  For irreducibility, use Hartshorne's
closed-fibre argument, equivalently the existing general lemma that the range
of a separately continuous map from two irreducible spaces is irreducible.

## Depends on

- [Algebraic sets](../../affine-varieties/algebraic-set.md)
- [Affine and quasi-affine varieties](../../affine-varieties/affine-variety.md)

## Proof depends on

- [The Zariski topology on affine space](../../affine-varieties/zariski-topology.md)

## Sources

- [Hartshorne I.3, Exercise 3.15(a), and I.7, proof of Proposition 7.1](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
