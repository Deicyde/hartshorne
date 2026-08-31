---
declaration: theorem
origin: cited
---

# Regular functions are continuous

A regular function `f : Y → k` is continuous when `k` carries the Zariski
topology of `𝔸¹` (Lemma 3.1). Consequently, if two regular functions on a
variety agree on some nonempty open subset then they agree everywhere
(Remark 3.1.1).

For continuity it suffices that `f⁻¹(a)` is closed for each `a ∈ k`, since the
closed sets of `𝔸¹` are the finite sets. Closedness is local, and on an open `U`
where `f = g/h` one has `f⁻¹(a) ∩ U = Z(g − ah) ∩ U`.

The corollary is the identity principle for varieties, and it carries far more
weight than its proof suggests: it is what makes `𝒪(Y) → 𝒪_P → K(Y)` injective,
so that all three rings can be treated as subrings of `K(Y)`. Every later
argument in the section that manipulates germs as if they were functions relies
on it.

## Depends on

- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)
- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)

## Sources

- [Hartshorne I.3, Lemma 3.1 and Remark 3.1.1 (p. 15)](../../sources/hartshorne.md#i3)
