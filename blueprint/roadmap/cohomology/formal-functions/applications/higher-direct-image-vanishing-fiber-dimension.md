---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Higher direct images vanish above the fibre dimension

Let `f : X -> Y` be a projective morphism of Noetherian schemes, let `F` be a
coherent `O_X`-module, and set

`r = max { dim X_y | y in Y }`.

Then `R^i f_* F = 0` for every `i > r`.

The bound concerns the dimensions of the scheme-theoretic fibres. No
flatness assumption on `F` or `f` is made.

## Depends on

- [The theorem on formal functions](../core/theorem-on-formal-functions.md)
- [Faithfulness of maximal-adic completion on finite modules](../core/maximal-adic-completion-faithful-finite.md)
- [Grothendieck vanishing](../../sheaf-cohomology/grothendieck-vanishing/grothendieck-vanishing.md)
- [Coherence of projective higher direct images](../../higher-direct-images/projective-higher-direct-images-coherent.md)

## Proof depends on

- Every infinitesimal fibre has the same underlying topological space and
  hence the same dimension as the ordinary fibre.
- Formal functions makes the completed stalk of `R^i f_*F` zero; coherence
  makes the stalk finite, so faithful completion reflects its vanishing.

## Sources

- [Hartshorne III.11, Corollary 11.2, p.279](../../../../sources/hartshorne-iii-11-12.md#applications-of-formal-functions-pp279281)
