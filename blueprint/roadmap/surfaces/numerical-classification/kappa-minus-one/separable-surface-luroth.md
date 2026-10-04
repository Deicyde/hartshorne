---
article_id: af_df08ac771d2a48bb0bd6a0de
declaration: theorem
origin: background
source_units: [chapter-v-section-6]
not_ready: true
---

# The separable surface Lüroth theorem

Let `k` be algebraically closed and let

`k subset L subset k(t,u)`

be fields such that `k(t,u)/L` is finite and separable.  Then `L` is a purely
transcendental extension of `k` of transcendence degree two.

This node is not ready.  Besides the blocked Castelnuovo criterion, the proof
requires an exact arbitrary-characteristic source for a nonsingular
projective surface model of `L` and for the separable invariant-descent
package.  The conclusion is not an instance of the one-variable Lüroth
theorem in Mathlib.

## Depends on

- [Separable descent of surface invariants](separable-generically-finite-invariant-descent.md)
- [Castelnuovo's rationality criterion](castelnuovo-rationality-criterion.md)

## Proof depends on

- Choose smooth projective models of `L` and `k(t,u)`.  The latter is
  rational, so its geometric genus, irregularity, and second plurigenus
  vanish.  Descent gives the same vanishing on the model of `L`, and
  Castelnuovo makes that model rational.

## Sources

- [Hartshorne V.6, Remark 6.2.1, p.422](../../../../sources/hartshorne-v-6.md)
- Serre [13] and Zariski [9].
