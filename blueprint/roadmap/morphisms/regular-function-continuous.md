---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isClosed_eqLocus Hartshorne.eq_of_eqOn_isOpen
---

# Regular functions are continuous

A regular function `f : Y → k` is continuous when `k` carries the Zariski
topology of `𝔸¹` (Lemma 3.1). Consequently, if two regular functions on a
variety agree on some nonempty open subset then they agree everywhere
(Remark 3.1.1).

Hartshorne's proof has two steps. First, closedness is local, and on an open `U`
where `f = g/h` one has `f⁻¹(a) ∩ U = Z(g − ah) ∩ U`, so every fibre is closed.
Second, the closed sets of `𝔸¹` are the finite sets, so closed fibres give
continuity.

**What is formalized here is the first step and the consequence, not the literal
statement.** `isClosed_eqLocus` proves the agreement locus of two regular
functions is closed, which is the first step in the form that gets used, and
`eq_of_eqOn_isOpen` is Remark 3.1.1. The second step needs a topology on `k`
identified with the one on `Unit → k`, plus the fact that a nonzero univariate
polynomial has finitely many roots. Nothing in §§1–3 uses continuity as such:
every later appeal is to the identity principle. That step is therefore deferred
rather than done for its own sake, and this article does not claim it.

The identity principle carries far more weight than its proof suggests: it is
what makes `𝒪(Y) → 𝒪_P → K(Y)` injective, so that all three rings can be
treated as subrings of `K(Y)`. Every later argument in the section that
manipulates germs as if they were functions relies on it.

## Depends on

- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)
- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)

## Sources

- [Hartshorne I.3, Lemma 3.1 and Remark 3.1.1 (p. 15)](../../sources/hartshorne.md#i3)
