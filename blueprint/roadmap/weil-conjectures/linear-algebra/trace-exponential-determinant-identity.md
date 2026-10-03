---
declaration: theorem
origin: cited
source_units: [appendix-c-section-4]
---

# Trace exponential equals reciprocal determinant

Let `phi` be an endomorphism of a finite-dimensional vector space `V` over a
field of characteristic zero. As formal power series,

`exp(sum_(r>=1) Tr(phi^r)*t^r/r) = det(1-t*phi)^(-1)`.

The characteristic-zero hypothesis makes the denominators `1/r` and the
formal exponential meaningful; the application is over `Q_ell`.

## Depends on

- This is a foundational finite-dimensional linear-algebra and formal-power-
  series leaf with no roadmap prerequisite.

## Proof depends on

- Prove the one-dimensional geometric-series logarithm identity and use an
  invariant line after scalar extension to an algebraic closure; traces and
  determinants are multiplicative/additive across the resulting short exact
  sequence.

## Sources

- [Hartshorne Appendix C.4, Lemma 4.1, p.455](../../../sources/hartshorne-appendix-c-4.md#linear-algebra-lemmas-printed-pp455456)
