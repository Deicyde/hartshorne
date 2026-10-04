---
article_id: af_bf2c13afb69f4bbe0b3293cb
declaration: theorem
origin: cited
source_units: [appendix-a-exercises]
not_ready: true
---

# Proper generically finite pushforward preserves linear equivalence

Let `f:X->X'` be a proper generically finite morphism of normal varieties.
If Weil divisors `D_1,D_2` on `X` are linearly equivalent, then their cycle
pushforwards `f_*D_1,f_*D_2` are linearly equivalent on `X'`.

This is the codimension-one input needed for proper pushforward to descend
from raw cycles to Chow groups. It is not ready: the existing finite-curve
pushforward theorem does not provide the higher-dimensional finite-flat norm
and divisor formula required here.

## Depends on

- [Raw-cycle pushforward](../raw-cycle-pushforward.md)
- [Codimension-one rational equivalence is linear equivalence](../codimension-one-rational-equals-linear.md)

## Proof depends on

- Remove a codimension-at-least-two subset of the normal target so that the
  morphism is finite flat, apply a sourced higher-dimensional norm/divisor
  formula there, and extend the Weil-divisor equality uniquely across the
  removed subset.

## Sources

- [Hartshorne Appendix A, Exercise 6.2, p.436](../../../../../sources/hartshorne-appendix-a-4-5.md#exercise-disposition-printed-pp436437)
