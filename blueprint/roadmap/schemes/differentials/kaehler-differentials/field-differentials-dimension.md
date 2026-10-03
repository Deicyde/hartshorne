---
declaration: theorem
origin: background
source_units: [chapter-ii-section-8]
---

# Differentials of finitely generated field extensions

Let `K/k` be a finitely generated field extension.  Prove

`trdeg_k K ≤ dim_K Ω[K⁄k]`,

with equality if and only if `K/k` is separably generated.  In particular, for
a finite algebraic extension, `Ω[K⁄k] = 0` exactly when the extension is
separable.

## Depends on

- [The universal module of Kähler differentials](kahler-differential-universal.md)

## Proof depends on

- Transcendence bases and the exact sequence for the tower from `k` through
  the corresponding rational function field to `K`.
- Mathlib's separably-generated-field infrastructure; no exact upstream
  dimension theorem was found.
- Matsumura [2], Theorem 59, p. 191, as cited by Hartshorne.

## Sources

- [Hartshorne II.8, Theorem 8.6A, printed p. 174](../../../../sources/hartshorne-ii-8.md)
