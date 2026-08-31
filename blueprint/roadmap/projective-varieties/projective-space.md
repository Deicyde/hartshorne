---
declaration: def
origin: cited
---

# Projective space

Projective `n`-space `ℙⁿ` over `k` is the set of equivalence classes of
`(n+1)`-tuples `(a₀,…,aₙ) ∈ kⁿ⁺¹ ∖ {0}` under `(a₀,…,aₙ) ∼ (λa₀,…,λaₙ)` for
`λ ∈ k^×`. A representative tuple is a set of *homogeneous coordinates* for the
point.

Mathlib has `Projectivization k V` for a vector space `V`, which is this
quotient for `V = kⁿ⁺¹`, together with its basic API. Reuse it rather than
introducing a second quotient; the work here is fixing `V = Fin (n+1) → k`,
naming the coordinate functions, and providing the `aᵢ ≠ 0` predicates that the
standard charts need.

Nothing topological happens yet: `ℙⁿ` is a set at this stage, and the Zariski
topology arrives two nodes later.

## Depends on

- Nothing in this roadmap.

## Sources

- [Hartshorne I.2, definition of projective `n`-space (pp. 8-9)](../../sources/hartshorne.md#i2)
