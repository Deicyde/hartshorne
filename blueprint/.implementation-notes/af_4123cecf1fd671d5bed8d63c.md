# Divisors of homogeneous fractions on Proj of a graded domain

## Status

New article from the quadric-surface-class-group split (roadmap proposal). No
general Lean exists yet; nothing is recorded in the frontmatter. Formalize
should record declarations here only after independent review.

## Existing Lean to generalize

- Polynomial-ring special case, module `Hartshorne.Scheme.ProjectiveSpaceClassGroup`:
  `Hartshorne.homogeneousFraction` (the germ at the generic point of
  `hypersurfaceChartEquation g h` on `D₊(h)`),
  `algebraMap_germ_hypersurfaceChartEquation`, `exists_eq_homogeneousFraction`,
  `homogeneousFraction_mul`, `ord_homogeneousFraction_eq_zero`,
  `ord_homogeneousFraction_eq_one`. These compute orders through the stalk
  `S_(𝔭)` (`Proj.stalkIso`), not through a degree-one chart; the chart form
  is what the quadric needs.
- Quadric single-chart pullback, module `Hartshorne.Scheme.QuadricSurfaceClassGroup`:
  `quadricChartι`, `quadricChartPull`, `ord_quadricChartPull` (order of a
  rational function on `Q` equals its order on the chart `D₊(s₀u₀)`, via
  `Scheme.ord_genericFunctionFieldMap` and the open-immersion stalk lemmas from
  the affine-line-invariance module).
- Mathlib: `AlgebraicGeometry.Proj.awayι`, `Proj.awayToSection`,
  `Proj.awayMap_awayToSection`, `Proj.basicOpenIsoSpec`, `Proj.stalkIso`,
  `AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen`,
  `AlgebraicGeometry.Scheme.ord` (`Mathlib/AlgebraicGeometry/OrderOfVanishing.lean`).
  No Mathlib result states the chart comparison.

## Candidate declarations (names are suggestions)

A new module, say `Hartshorne.Scheme.ProjHomogeneousFraction`, for a graded
domain `𝒜 : ℕ → Submodule R S` with `Proj 𝒜` satisfying `(*)`:

1. `Hartshorne.projHomogeneousFraction (hg : g ∈ 𝒜 d) (hh : h ∈ 𝒜 d) (h0 : h ≠ 0) :
   (Proj 𝒜).functionField`, generalizing `homogeneousFraction`.
2. `Hartshorne.projHomogeneousFraction_awayι` (or `…_eq_chartFraction`): for
   `f ∈ 𝒜 1`, `f ≠ 0`, the image of `projHomogeneousFraction` under the
   function-field map of `Proj.awayι 𝒜 f` is
   `algebraMap _ _ (g/f^d) / algebraMap _ _ (h/f^d)` in the fraction field of
   `Away 𝒜 f`.
3. `Hartshorne.ord_projHomogeneousFraction`: for a coheight-one point `x` in
   `D₊(f)` with corresponding point `v` of `Spec (Away 𝒜 f)`,
   `(Proj 𝒜).ord (projHomogeneousFraction …) x` equals the order at `v` of the
   dehomogenized numerator minus that of the dehomogenized denominator.

Afterwards the polynomial case in `ProjectiveSpaceClassGroup` and the quadric
case could be rewritten as instances; that refactor is optional.

## Uses

Serves goals 1 and 2 of the quadric class-group leaf (every ruling line has
class `(1,0)` or `(0,1)`; every hyperplane section has class `(1,1)`): e.g.
`s₀u₀ / s₁u₀` has divisor `L₁ - {s₁ = 0}`, and `ℓ / s₀u₀` for a linear form `ℓ`
compares a hyperplane section with `L₁ + L₂`.
