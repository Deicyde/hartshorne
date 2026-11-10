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

## Plan (stalk route)

At a stalk, `F''_x` is free of arbitrary rank (stalk of `⊕_I 𝒪` is `⊕_I 𝒪_x`), so
`0 → F'_x → F_x → F''_x → 0` splits with free outer terms.
1. Module level, for free modules of arbitrary rank (DONE in this branch, not yet compiled):
   `ExteriorPowerFiltration.phiSum_injective_of_free`, by reduction to finite sub-bases
   (`subBasisMap`, `subBasisCoord`, `exists_mem_range_exteriorPower_map`, naturality `srcMap*`,
   `map_comp_phiSum`, `phiSum_comp_srcMap`). `eq_zero_of_phi_mem_filt` and
   `alpha_mem_filt_succ_iff` now need only `Module.Free` (no `Module.Finite`).
2. Stalks: an exterior-power analogue of `presheafTensorStalkIso` (ModuleSheafTensor.lean),
   `(⋀^n P)_x ≅ ⋀^n (P_x)`, compatible with `extMap`, `alphaPre` and `betaPre`. Alternatively
   just the germ-level injectivity of `⋀^n (sections) → ⋀^n (stalk)` along the filtered colimit.
3. Show that the stalk maps of `toGrad`/`toH` are bijective, by the module-level result for the
   stalk sequence (split, free outer terms). Use `SheafAlgebraOperations.isIso_sheafifyMap`
   (stalk bijectivity) in place of `isIso_sheafifyMap_of_locally_bijective`.
4. Stalks of a locally free sheaf of arbitrary rank are free.
5. New theorems `exteriorPower_exact_filtration_of_isLocallyFree` (and `exists_...`) with
   `Ringed.IsLocallyFree`. The old ones are deprecated and derived from them;
   `exteriorPower_exact_det` keeps finite ranks.
6. Then the Roadmap commit (retract, restate toward the book), and re-record after evidence and
   r9-44.
