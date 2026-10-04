---
article_id: af_fb49c16fd15cb8723672d484
declaration: theorem
origin: cited
source_units: [chapter-v-section-2]
---

# A ruled surface is a rank-two projective bundle

Let `pi : X -> C` be a ruled surface and let `D` be the image of a section.
Then `E = pi_* O_X(D)` is locally free of rank two, evaluation is a
surjection `pi^* E -> O_X(D)`, and the resulting quotient-line morphism is
an isomorphism

`X ~= P_C(E)`

over `C`.

## Depends on

- [Pushforward in nonnegative fibre degree](ruled-pushforward-nonnegative-fibre-degree.md)
- [The tautological quotient on a projective bundle](../../../schemes/projective-geometry/relative-proj-bundles/projective-bundle-tautological-quotient.md)
- [Cohomology and base change](../../../cohomology/semicontinuity/theorems/cohomology-and-base-change.md)

## Proof depends on

- The evaluation map is fibrewise the globally generated `O_P1(1)`.
- The quotient-line morphism restricts to an isomorphism on every fibre;
  the proper fibrewise-isomorphism criterion makes it an isomorphism over
  `C`.

## Sources

- [Hartshorne V.2, Proposition 2.2, p.370](../../../../sources/hartshorne-v-2.md)
