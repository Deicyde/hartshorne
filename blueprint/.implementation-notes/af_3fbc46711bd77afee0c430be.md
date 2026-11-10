# Exterior powers of an exact sequence (faithfulness item 6: arbitrary rank)

## Status

In progress on branch faith/item6 (based on 9da24f47). The recorded Lean (finite rank) is
unchanged and the article is NOT retracted. Retract it only once the generalized Lean compiles.

Revision-contract impact (`autoform work impact`): not contained. canonical-sheaf-projective-space
is proof-impacted (through `exteriorPower_exact_det`/filtration), so use expand-migrate-contract:
new names with `Ringed.IsLocallyFree`, the old names `@[deprecated]` and derived through
`IsFiniteLocallyFree → IsLocallyFree`, and `lean:` pointing at the new names.

## Why the current proof does not generalize

`gradedIso` needs `hloc`: near every point, on all small opens `V`, the sequence of sections
`0 → F'(V) → F(V) → F''(V) → 0` is split with free outer terms (`IsSplitAt`), which feeds
`toGrad_bijective`/`toH_bijective` and `isIso_sheafifyMap_of_locally_bijective`. In infinite rank
this fails: sections of a free sheaf `⊕_I 𝒪` over an open are not a free module, and infinitely
many basis sections cannot be lifted on a common neighbourhood.

The per-section route (split over a finite free sub-summand of `F''`) handles three of the four
germ-level statements: `toGrad` surjective (already sectionwise, from `filt_of_le`), `toH`
surjective (finitely many local lifts), and `toH` injective (a partial splitting `s_J ∘ c_J`
suffices for `β z = 0 ⇒ α z ∈ F^{p+1}`). The fourth, `toGrad` injective
(`α z ∈ F^{p+1} ⇒ β z = 0`, the `phiSum`-injectivity direction), needs to transport a membership
in `F^{p+1}(W) ⊆ ⋀^r F(W)` back to a finite free summand `M₀`. That requires `⋀^r M₀ → ⋀^r F(W)`
to be injective (a retraction of `F(W)` onto `M₀`), which needs a splitting of `F(W) → F''(W)` on
all of `F''(W)`. That splitting does not exist on sections.

## Plan (stalk route) and progress

At a stalk, `F''_x` is free of arbitrary rank, so `0 → F'_x → F_x → F''_x → 0` splits with free
outer terms.

Proved and compiling (branch head faith/item6):
1. Module level, free modules of arbitrary rank (commit 2ba12c24,
   src/Hartshorne/Scheme/ExteriorPowerFiltrationAlgebra.lean):
   `ExteriorPowerFiltration.phiSum_injective_of_free`, by reduction to finite sub-bases
   (`subBasisMap`, `subBasisCoord`, `exists_mem_range_exteriorPower_map`, `srcMap`,
   `map_comp_phiSum`, `phiSum_comp_srcMap`, `range_srcMap_mono`, `exists_mem_range_srcMap`).
   `eq_zero_of_phi_mem_filt` and `alpha_mem_filt_succ_iff` now need only `Module.Free`, with no
   `Module.Finite`. The downstream modules ExteriorPowerExactFiltration and
   CanonicalSheafProjectiveSpace still build.
2. Stalks of a locally free module of arbitrary rank are free (commit bcc44f8a,
   src/Hartshorne/RingedSpace/LocallyFreeRank.lean): `Ringed.moduleStalk_free_of_isLocallyFree`.

3. Exterior powers commute with stalks (commit 60bc72b7, section `ExteriorStalk` of
   src/Hartshorne/Scheme/ExteriorPowerExactFiltration.lean): `extStalkEquiv n F x :
   ⋀^n (F_x) ≃ₗ[𝒪_{X,x}] (⋀^n F)_x`, with `extStalkEquiv_symm_germ` (germ of `y` ↦ `extGerm y`).
   Helpers: `exists_open_le_of_finite`, `exists_common_sectionGerm`, `germₛₗ`, `extGerm`,
   `extGerm_ιMulti`, `extGerm_res`, `extStalkToExt(_germ/_smul)`, `sectionGerm_ιMulti_res`,
   `sectionGerm_ιMulti_indep`, `extStalkMulti(_eq)`, `extStalkAlt`, `extToExtStalk`.

(Commit ee4acede in the branch history is a WIP snapshot that does not compile by itself. The
head does compile.)

Remaining:
4. Stalk bijectivity of `toGrad` and `toH`, to feed `SheafAlgebraOperations.isIso_sheafifyMap`
   in place of `isIso_sheafifyMap_of_locally_bijective`:
   - Stalk exactness of `0 → F'_x → F_x → F''_x → 0` follows from `app_injective_of_mono`,
     `range_eq_ker_of_shortExact` and `exists_local_lift`, by germs. The splitting comes from
     freeness of `F''_x` (projective).
   - `toGrad` surjective: already sectionwise.
   - `toGrad` injective: if `α z ∈ F^{p+1}(W)`, then at the stalk `α_x(z_x) ∈ filt_x(p+1)`. So
     `β_x(z_x) = 0` (`alpha_mem_filt_succ_iff` at the stalk), hence `(β z)_x = 0` by injectivity
     of step 3, hence `β z = 0` near `x`.
   - `toH` injective: if `(β z)_x = 0`, then `α_x(z_x) = α'_x(w̄)`. Lift `w̄` to sections by
     surjectivity of step 3; then `α z = α' w` near `x`.
   - `toH` surjective: `lTensor_map_surjective` at the stalk, then lift by step 3.
5. New theorems `exteriorPower_exact_filtration_of_isLocallyFree` (and `exists_...`) with
   `Ringed.IsLocallyFree`, and a `gradedIso` variant without `hloc`. The old names become
   `@[deprecated]`, derived through `IsFiniteLocallyFree.isLocallyFree`.
   `exteriorPower_exact_det` keeps its finite ranks.
6. Then the Roadmap commit (retract and restate as the lead specified, and update
   hartshorne-ii-5.md if it says finite rank for Ex. 5.16), then evidence, r9-44 and re-record.
