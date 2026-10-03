---
declaration: isomorphism
origin: cited
source_units: [chapter-iii-sections-8-9]
---

# The acyclic Leray comparison

Let `f : X -> Y` be a continuous map and let `F` be an abelian sheaf on `X`.
If `R^q f_* F=0` for every `q>0`, then for every `p` construct the natural
isomorphism

`H^p(Y,f_*F) ~= H^p(X,F)`.

This is Exercise 8.1. The unique result is only the acyclic comparison; the
roadmap does not claim or depend on a full Leray spectral sequence.

## Depends on

- [Higher direct images of abelian sheaves](higher-direct-images.md)
- [Sheaf cohomology and the Ext model](../sheaf-cohomology/sheaf-cohomology.md)

## Proof depends on

- [Acyclic resolutions compute derived functors](../derived-functors/acyclic-resolution-comparison.md)
- Exactness of inverse image for abelian sheaves and the generic adjunction
  theorem that a right adjoint to an exact functor preserves injectives.
- Choose an injective resolution `F -> I^.`. The terms `f_* I^n` are
  injective, and `H^q(f_*I^.)` computes `R^q f_*F`. The vanishing hypothesis,
  together with `R^0 f_*F ~= f_*F`, therefore makes
  `f_*F -> f_*I^.` an injective resolution.
- The section identity `Gamma(Y,f_*I)=Gamma(X,I)` identifies the two
  cochain complexes whose cohomology gives the comparison.

## Sources

- [Hartshorne III, Exercise 8.1, printed p.252](../../../sources/hartshorne-iii-8.md#retained-exercise-81-printed-p-252)
- Godement, II.4.17.1, for the general Leray spectral sequence cited by Hartshorne; only its degenerate consequence is retained here.
