---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Fibre dimension of a coherent sheaf is upper semicontinuous

Let `Y` be a Noetherian scheme and `G` a coherent `O_Y`-module. The function

`y |-> dim_(k(y)) (G_y tensor_(O_(Y,y)) k(y))`

is upper semicontinuous: for every `y` there is an open neighbourhood `U`
such that its value at every `y' in U` is at most its value at `y`.
Equivalently, for every integer `n`, the locus where the value is at least `n`
is closed.

## Depends on

- [Coherent affine-local criterion](../../../schemes/modules-and-quasicoherent/coherent-affine-local-criterion.md)

## Proof depends on

- Nakayama's lemma identifies the fibre dimension with the minimal number of
  generators of `G_y`; a minimal generating set extends and generates on a
  neighbourhood because `G` is coherent.

## Sources

- [Hartshorne III.12, Example 12.7.2, p.288](../../../../sources/hartshorne-iii-11-12.md#semicontinuity-grauert-and-base-change-pp287291)
