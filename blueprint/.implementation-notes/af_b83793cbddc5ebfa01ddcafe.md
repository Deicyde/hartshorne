# Projectively normal Veronese embeddings — implementation note

Module: `Hartshorne/Scheme/ProjectivelyNormalVeronese.lean` (namespace
`Hartshorne.ProjectivelyNormalVeronese`, imported by the library root).

## Statement

`exists_isProjectivelyNormal_image_projDupleMap`: for `k` algebraically closed and a closed
immersion `f : X ⟶ Proj k[x₀, …, xᵣ]` with `X` connected and normal, there is `d₀ > 0` such that
for every `d ≥ d₀` (with a `[NeZero d]` binder) the closed subscheme of `ℙᴺ_k = Proj k[y_I]` with
ideal sheaf `ker (f ≫ ρ_d)` is projectively normal (`ProjectiveNormality.IsProjectivelyNormal`,
recorded on projective-normality-criterion: its homogeneous coordinate ring
`k[y_I] / (Γ_*(ℐ) ∩ k[y_I])` is an integrally closed domain).

The `d`-uple map is `projDupleMap d : Proj k[x] ⟶ Proj k[y_I]`, defined as
`Veronese.projIso` followed by `Proj.map` of the graded map `y_I ↦ x^I`
(`dupleMapHom`, the `I` enumerated by `Veronese.dupleEquiv`). The `d`-uple embedding of
`X = Proj (S/I)` is `projDupleEmbedding I d`, the same construction for `S/I`;
`projQuotientι_comp_projDupleMap` shows it is the restriction of `projDupleMap d` (naturality
`Veronese.map_comp_toProj`).

Not proved: the comparison of `projDupleMap` with `Veronese.dupleMap d r (Spec k)` (defined over
`ℤ` by base change, landing in `projectiveSpaceOverScheme`) through `projectiveSpaceOverSpecIso`.
Both are "monomials of degree `d`"; the comparison is bookkeeping across the two models of `ℙⁿ`.

## Route (the book's)

1. Exercise 5.14(a) (`ProjectiveSectionRing.projectiveSectionRing_isIntegralClosure`): `S/I` is a
   domain and `S' = ⨁_{n ≥ 0} Γ(X, 𝒪_X(n))` is its integral closure in `K = Frac(S/I)`.
2. Exercise 5.14(b), `exists_mem_algebraMap_eq_sectionToFraction`: by Exercise 5.9
   (`EventualSectionRecovery.exists_bijective_alphaComponent` for the graded module
   `gradedTwist 𝒬 0`, then `bijective_alphaComponent_iff`, `bijective_constHom_iff`,
   `bijective_constHom0_congr` to reach `projTwistingSheaf 𝒬 n`), every section of `𝒪_X(n)`,
   `n ≥ n₀`, is `s / 1` with `s ∈ (S/I)_n`. Algebra structure `k → (S/I)₀` is a local `let`.
3. Degree `0` (not covered by Exercise 5.9): an element of `K` homogeneous of degree `0` and
   integral over `S/I` is integral over `(S/I)₀` (degree-`0` parts of the coefficients after
   `Polynomial.scaleRoots`, private `exists_monic_coeff_mem_zero`), hence in `k` since `k` is
   algebraically closed (`minpoly.mem_range_of_degree_eq_one`). This is where `IsAlgClosed k` is
   used.
4. The plain-text prerequisite "a sufficiently high Veronese subring of a graded normal domain is
   normal" is proved here, as `isIntegrallyClosed_veroneseSubring`: a criterion phrased in `K`
   (every integral element is a finite sum of homogeneous fractions with a property `P`, and those
   of degree divisible by `d` lie in `A`). Key step `sum_filter_not_dvd_eq_zero`: the components
   of degree prime to `d` vanish (common denominator of degree divisible by `d`, then the additive
   projection onto degrees prime to `d`, private `offProj`, commutes with multiplication by
   elements of `A^{(d)}`).
5. `exists_isIntegrallyClosed_veroneseSubring`: `(S/I)^{(d)}` is integrally closed for
   `d ≥ max n₀ 1`.
6. Coordinate ring of the image: `dupleIdeal I d = ker (y_I ↦ x^I : k[y_I] → S/I)`, homogeneous
   (`isHomogeneous_ker_dupleHom`); `dupleQuotientEquiv : k[y_I] / J_d ≃+* (S/I)^{(d)}`
   (surjectivity from `Veronese.adjoin_dupleCoords`); `J_d` saturated
   (`mem_dupleIdeal_of_pow_mul_mem`), so `Γ_*(ker (Proj (k[y]/J_d) ⟶ ℙᴺ)) ∩ k[y] = J_d`
   (`ProjectiveClosedSubscheme.gammaStarIdeal_ker_projQuotientι`).
7. `projDupleEmbedding_eq`: `projDupleEmbedding I d` is `Veronese.projIso` followed by the
   isomorphism `Proj (S/I)^{(d)} ≅ Proj (k[y]/J_d)` (`isIso_map_dupleQuotientHom`, via
   `isIso_projPartialMap_of_bijective`, as in `QuadricSurfaceSegre`) and `projQuotientι J_d`; so
   `ker_projDupleEmbedding`. The final theorem transports along
   `ProjectiveClosedSubscheme.exists_iso_projQuotientι_gammaStarIdeal` (connectedness and
   normality move along the isomorphism).

## Links added

- Depends on projective-normality-criterion (definition `IsProjectivelyNormal`).
- Proof depends on projective-ideal-saturation (`saturation_gammaStarIdeal`,
  `gammaStarIdeal_ker_projQuotientι`, `le_saturation`, `mem_saturation`).
