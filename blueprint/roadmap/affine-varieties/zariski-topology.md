---
declaration: instance
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.zariskiTopology Hartshorne.zeroSet_union_zeroSet Hartshorne.isAlgebraicSet_sInter Hartshorne.isClosed_iff_isAlgebraicSet
---

# The Zariski topology on affine space

The union of two algebraic sets is algebraic, the intersection of an arbitrary
family of algebraic sets is algebraic, and both `∅` and `𝔸ⁿ` are algebraic
(Proposition 1.1). Therefore taking the algebraic sets as the closed sets
defines a topology on `𝔸ⁿ`, the *Zariski topology*.

The main result of this node is the topology instance; Proposition 1.1 is the
closure property that justifies it and should land with it. Note that the union
case is the only one with content: `Z(T₁) ∪ Z(T₂) = Z(T₁T₂)`, where `T₁T₂` is
the set of pairwise products, and the reverse inclusion uses that `k` is a
domain.

This topology is not Hausdorff, and none of the separation axioms Mathlib's
topology library reaches for by default apply. Expect to supply `IsClosed`
lemmas directly rather than through a metric or order structure.

## Depends on

- [Algebraic sets](algebraic-set.md)

## Sources

- [Hartshorne I.1, Proposition 1.1 and the definition of the Zariski topology (p. 2)](../../sources/hartshorne.md#i1)
