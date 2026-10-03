---
declaration: theorem
origin: cited
source_units: [chapter-v-section-2]
---

# Stability of normalized rank-two bundles

For a locally free sheaf `E` on a curve, use Hartshorne's quotient convention:
`E` is stable (respectively semistable) when every nonzero proper locally
free quotient `E -> F` satisfies

`deg(F)/rank(F) > deg(E)/rank(E)`

(respectively `>=`). A decomposable bundle is never stable.

If `E` has rank two and is normalized in the sense of Proposition V.2.8,
then `E` is stable exactly when `deg(E)>0`, and semistable exactly when
`deg(E)>=0`. Equivalently for the ruled invariant `e=-deg(E)`, stability is
`e<0` and semistability is `e<=0`.

## Depends on

- [Normalized projective-bundle existence](../normalization/normalized-projective-bundle-existence.md)
- [The normalized ruled-surface invariant](../normalization/normalized-ruled-surface-invariant.md)

## Proof depends on

- Translate quotient inequalities to degrees of invertible quotients and use
  normalization to control the degrees of their kernels after twisting.
- A direct-sum projection violates the strict slope inequality for one of the
  two summands.

## Sources

- [Hartshorne V.2, Exercise 2.8(a,b), p.384](../../../../sources/hartshorne-v-2.md#exercise-disposition-printed-pp383386)
