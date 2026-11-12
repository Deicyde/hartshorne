# The differential principal-parts resolution

## Status: candidate formalization (pending review)

Lean modules:

- `Hartshorne/Scheme/Differentials/GenericDifferentials.lean`: generic values of differentials on
  an integral scheme over a field.
- `Hartshorne/Cohomology/CurveDifferentialPrincipalParts.lean`: the resolution on a nonsingular
  curve.

## Declarations

- `Hartshorne.curveDifferential_principalPartsResolution`: the main statement. For
  `X.IsNonsingularCurve k` with `k` algebraically closed it gives:
  - the stalk map `(Ω_{X/k})_P → Ω_{K/k}` is injective with image `differentialsStalkRange`, the
    subgroup used for `Ω_{K/k}/Ω_{X,P}`;
  - the complex `differentialPrincipalPartsComplex` is short exact;
  - its last two terms are flasque;
  - `differentialPrincipalPartsClosedCofan` (skyscrapers over the closed points) is a colimit;
  - `H¹(X, Ω_X) ≅ cokernel (Γ(⊤) of the principal-parts map)`.
- `Hartshorne.sheafCohomology_one_curveDifferentials_iso_cokernel`: the cokernel description of
  `H¹` on its own.
- Objects: `curveDifferentialsSheaf` (the abelian sheaf of `Scheme.relativeDifferentials`),
  `rationalDifferentialsSheaf` (`constantSheaf` with value `functionFieldDifferentials`),
  `differentialPrincipalPartsSheaf` (`locallyFiniteSumSheaf` of
  `differentialPrincipalPartsGroup`), the maps `differentialsToRational` and
  `rationalToPrincipalParts`, and the complex `differentialPrincipalPartsComplex`.

## Route

- `Ω_K` is made into an `𝒪_X`-module (`genericConstantModule`: sections act through their germs
  at the generic point). Then `a ↦ d(a_η)` is a relative derivation (`genericDerivation`). Its
  vanishing on the inverse image of `𝒪_{Spec k}` uses the same subsheaf-factorization trick as
  `AffineRelativeDifferentials`. The universal property of `Scheme.relativeDifferentials` gives
  `differentialsToGeneric`.
- The generic values form a `K`-submodule that contains `d K`, so every rational differential is a
  generic value (`exists_differentialsToGeneric_eq`).
- `Ω_{K/k} ≠ 0`: by `Algebra.FormallyUnramified.isSeparable` and `trdeg = 1`, which comes from
  `exists_dim_eq_trdeg_of_isAffineOpen` and `ringKrullDim_stalk_of_isClosed`.
- Injectivity uses the local triviality `Ω|_W ≅ 𝒪_W`, obtained from
  `isRegular_iff_relativeDifferentials_isLocallyFreeOfRank` and `coproductUniqueIso`. Every
  section is `a • ω₀`, and the image of `ω₀` is nonzero.
- Exactness in the middle is checked on stalks, by gluing local preimages. Epi comes from local
  surjectivity (`TopCat.Sheaf.isLocallySurjective_iff_epi`). Flasqueness uses
  `isFlasque_constantSheaf_of_irreducibleSpace` and `isFlasque_locallyFiniteSumSheaf`. `H¹` comes
  from the long exact sequence and `ShortComplex.Exact.gIsCokernel`.

## Notes

- Completeness of the curve is not used; the Lean statement holds for every nonsingular curve.
- The direct sum is indexed by all points, but the summand at the generic point is zero. The
  closed-point coproduct is `isColimitDifferentialPrincipalPartsClosedCofan`, by the general
  `isColimitCofanSubtypeOfIsZero`.
- `isFlasque_locallyFiniteSumSheaf` is recorded on projective-line-regular-sheaf-acyclic.
