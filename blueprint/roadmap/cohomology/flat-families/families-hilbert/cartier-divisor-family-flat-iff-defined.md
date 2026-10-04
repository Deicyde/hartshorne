---
article_id: af_61f0ede5a8f3756e05a14bf3
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-8-9]
not_ready: true
---

# Flat algebraic families of Cartier divisors

Let `X` be finite type over an algebraically closed field, `T` a nonsingular
curve, and `D` an effective Cartier divisor on `X times T`. The closed
subscheme `D` is flat over `T` if and only if the fibrewise intersection
Cartier divisor `D.X_t` is defined for every closed point `t`.

## Depends on

- [Effective Cartier divisors as closed subschemes](../../../schemes/divisors/cartier-picard/effective-cartier-closed-subscheme.md)
- [The stalk criterion for flat morphisms](../flatness/flat-morphism-stalk-criterion.md)

## Proof depends on

- Compare regularity of the pairs `(u,f)` and `(f,u)` in the local ring of
  `X times T`.
- [Flat modules over a PID are torsion-free modules](../flatness/pid-flat-iff-torsion-free.md).
- The two-element regular-sequence permutation theorem cited from Matsumura,
  *Commutative Algebra*, Theorem 28, p.102.

Pinned Mathlib explicitly leaves regular-sequence permutability as future
work, so this proof root is not ready.

## Sources

- [Hartshorne III.9, Example 9.8.5, p.261](../../../../sources/hartshorne-iii-9.md#dimensions-associated-points-and-flat-limits-pp256261)
