# The domain of a birational map has codimension-two complement

## Status

Not stated. The setting of the statement is not reachable from this article's
dependencies (valuative criterion for properness; codimension-one stalks are
DVRs), so no notion was chosen.

## Missing prerequisites

- Scheme-level rational and birational maps and the maximal domain of
  definition. No blueprint article records them. The pinned Mathlib has
  `AlgebraicGeometry.Scheme.RationalMap` (notation `X ⤏ Y`),
  `Scheme.RationalMap.domain` (the union of the domains of all
  representatives, with `RationalMap.mem_domain`), `RationalMap.IsOver`, and
  `Scheme.PartialIso` / `Scheme.BirationalOver` in
  `Mathlib/AlgebraicGeometry/Birational/Birational.lean`. The project's
  `Hartshorne.BirationalMap` and `Hartshorne.BirationalMap.dom` are the
  classical Chapter I / V.5 notions on varieties, not schemes.
- Nonsingular abstract variety: `AlgebraicGeometry.Scheme.IsRegular`
  (schemes/differentials/scheme-differentials/regular-points-and-nonsingular-schemes)
  is formalized but not reachable.
- Abstract and proper varieties over k:
  schemes/proper-and-projective/abstract-complete-variety is not formalized
  and not reachable. Alternatively state the hypotheses inline: integral,
  separated and finite type (respectively proper) over `Spec k`.
- Codimension: `Hartshorne.codim` (schemes/subschemes-and-dimension/scheme-codimension)
  is already reachable.

## Proof route once the setting is fixed

- At a codimension-one point $x$ the stalk is a DVR with fraction field
  $K(X)$ (`Scheme.codimensionOneStalk_isDiscreteValuationRing`,
  `Scheme.functionField_isFractionRing_of_stalk_of_satisfiesConditionStar`).
  A nonsingular variety satisfies condition $(*)$.
- The rational map gives a $k$-morphism `Spec K(X) ⟶ X'`
  (`RationalMap.fromFunctionField`). The valuative criterion
  (`IsProper.eq_valuativeCriterion`, existence part) lifts it to
  `Spec 𝒪_{X,x} ⟶ X'` over `Spec k`.
- `Scheme.PartialMap.ofFromSpecStalk` (needs `LocallyOfFiniteType` of the
  target structure map and germ-injectivity, e.g. integral $X$) spreads the
  lift to a partial map defined at $x$ (`mem_domain_ofFromSpecStalk`).
- It agrees with the given rational map at the generic point
  (`fromSpecStalkOfMem_ofFromSpecStalk`, `RationalMap.eq_of_fromFunctionField_eq`),
  so it represents the same rational map and $x$ lies in its domain.
