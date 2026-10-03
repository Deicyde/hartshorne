---
declaration: theorem
origin: cited
source_units: [chapter-v-section-3]
---

# Higher direct images of the point-blowup structure sheaf vanish

For the monoidal transformation `pi:X_tilde->X`,

`R^i pi_* O_X_tilde = 0`

for every `i>0`.

## Depends on

- [The exceptional infinitesimal-neighborhood filtration](exceptional-infinitesimal-neighborhood-filtration.md)
- [The theorem on formal functions](../../../cohomology/formal-functions/core/theorem-on-formal-functions.md)
- [Faithfulness of maximal-adic completion](../../../cohomology/formal-functions/core/maximal-adic-completion-faithful-finite.md)
- [Top cohomology of projective-space twists](../../../cohomology/projective-cohomology/projective-space-top-twist-cohomology.md)
- [Coherence of projective higher direct images](../../../cohomology/higher-direct-images/projective-higher-direct-images-coherent.md)

## Proof depends on

- The filtration and `H^i(P^1,O(n))=0` for `i>0,n>=0` give
  `H^i(E_n,O_(E_n))=0` by induction.
- Formal functions makes the completed stalk at `P` zero. The higher direct
  image is coherent and supported at `P`, so faithful completion makes it
  zero; it already vanishes off `P`, where `pi` is an isomorphism.

## Sources

- [Hartshorne V.3, Proposition 3.4, pp.387–388](../../../../sources/hartshorne-v-3.md)
