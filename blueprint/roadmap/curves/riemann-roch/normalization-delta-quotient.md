---
article_id: af_fee62ec99afff5f65d12af06
declaration: exact sequence
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# The normalization defect quotient

Let `X` be an integral projective one-dimensional scheme over an
algebraically closed field and let `nu : X_tilde -> X` be its normalization.
There is an exact sequence of coherent sheaves

`0 -> O_X -> nu_* O_X_tilde -> Q -> 0`,

where `Q` has finite support and

`Q_P ~= Otilde_P / O_(X,P)`.

Here `Otilde_P` is the finite semilocal integral closure of `O_(X,P)` in
`K(X)`, namely the stalk `(nu_*O_X_tilde)_P`. Its localizations at maximal
ideals are the normalization local rings above `P`; it is not replaced by
their product. Define `delta_P` as the finite module length of this quotient;
only finitely many `delta_P` are nonzero.

## Depends on

- [Normalization](../../schemes/normalization-and-exercises/normalization-construction.md)
- [Normalization is finite over a finite-type field scheme](../../schemes/normalization-and-exercises/normalization-finite-type-field.md)
- [Finite pushforward preserves coherence](../../schemes/modules-and-quasicoherent/finite-pushforward-coherent.md)
- [Sections with support of a quasicoherent sheaf](../../schemes/coherent-sheaves/sections-with-support-quasicoherent.md)

## Proof depends on

- Normalization is an isomorphism over the normal locus, whose complement on
  a Noetherian integral curve is a finite set of closed points.
- On an affine neighbourhood of `P`, finite pushforward is restriction of
  scalars; localizing that finite algebra at `P` gives the semilocal integral
  closure whose maximal localizations are the normalization local rings above
  `P`.

## Sources

- [Hartshorne IV.1, Exercise 1.8 preamble, p.298](../../../sources/hartshorne-iv-1.md#exercise-disposition-printed-pp297298)
