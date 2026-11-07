# The relative twisting sheaf

## Status

Not recorded. The statement needs the gluing of sheaves of modules along the affine
pieces of the relative Proj, which neither the pinned Mathlib nor the project has
(Mathlib defines `Pseudofunctor.IsStack` but proves no stack instance for
`SheafOfModules`; the project's Exercise II.1.22 gluing handles sheaves valued in a
fixed category only). The roadmap revision below made that gluing its own article,
now under this leaf's "Depends on"; this leaf waits for it. Every other ingredient is
built, sorry-free, in two modules imported by the library root.

## Checked declarations

`Hartshorne.Scheme.ProjTwistLocalization` (namespace `Hartshorne.ProjTwistMap`),
for a graded map `φ : A → B` with `B₊ ≤ φ(A₊)B` and `f = Proj.map φ`:

- `twistFiber`, `twistFiber_mk`, `twistFiber_smul`, `twistFiber_comp`,
  `twistFiber_id`: the fiber maps `A(n)_(P) → B(n)_(Q)`, `m/t ↦ φm/φt`, linear over
  the local ring maps, functorial (stated with a pointwise hypothesis `φ'' = φ' ∘ φ`).
- `twistHom : projTwistingSheaf 𝒜 n ⟶ f_* projTwistingSheaf ℬ n` (no localization
  hypothesis), and for an open immersion `f` the adjoint
  `twistRestrictHom : (projTwistingSheaf 𝒜 n).restrict f ⟶ projTwistingSheaf ℬ n`
  with the pointwise formula `twistRestrictHom_app_apply` (rfl).
- For `B = A[1/s]`, `s ∈ A₀` (`[IsLocalization.Away s B]`, `φ = algebraMap`):
  `twistFiber_injective`, `twistFiber_surjective`, `fiberEquiv`,
  `isIso_twistRestrictHom`, `twistRestrictIso`. These are the candidate
  declarations of the split-off article "Twisting sheaves under localization in degree
  zero" (`af_71347b8169aa158ac22ab154`), now under this leaf's "Proof depends on"; that
  article's note records them, and this leaf does not.

`Hartshorne.Scheme.RelativeProjTwist` (namespace
`Hartshorne.QuasiCoherentGradedAlgebra`), for `S` and `n : ℤ`:

- `twistingSheaf S n U = projTwistingSheaf (S.grading U) n`.
- `twistTransitionHom S n f`, `isIso_twistTransitionHom`, `twistTransition`: for
  `f : U ⟶ V` in `X.AffineZariskiSite`,
  `(twistingSheaf V).restrict (Proj.map (S.restrict f) _) ≅ twistingSheaf U`.
- `twistTransitionHom_id`, `twistTransitionHom_comp`: identity and cocycle
  conditions, phrased with Mathlib's `restrictFunctorCongr`, `restrictFunctorComp`,
  `restrictFunctorId` and `projMap_restrict_comp` / `projMap_restrict_id`.
- `adjoin_eq_top_of_generatedInDegreeOne`, `isInvertible_twistingSheaf`: each piece
  is invertible under `GeneratedInDegreeOne`.

Restrictions are taken along `Proj.map (S.restrict f) (S.irrelevant_le f)`, not
`S.projFunctor.map f`: instance search does not find `IsOpenImmersion` for the latter
spelling, even with an instance stated for it.

## Remaining goal

Prove the gluing article "Gluing sheaves of modules along open immersions"
(`af_cc5b776dbee778ca137f2f01`), stated in Hartshorne's open-cover form. Then build the
overlap isomorphisms on `π⁻¹(U ∩ V)` from `twistTransition` (the descent data are
indexed by basic-open arrows of `X.AffineZariskiSite`, not by pairwise intersections;
glue the transition isomorphisms over basic opens lying in both `U` and `V`), check
the cocycle condition locally, and apply the gluing to the cover of `Proj_X S` by the
`projι U` with `M U = twistingSheaf S 1 U`. That yields `𝒪_{Proj_X S}(1)` with
`(projι U)^* 𝒪(1) ≅ twistingSheaf S 1 U`. Invertibility is local: transport
`isInvertible_twistingSheaf` along these isomorphisms (the `projι U` cover `relProj`).
The compatibility over an affine open `U ⊆ X` is the gluing isomorphism composed with
`restrictIso`, via `restrictFunctorComp` along `(Proj_X S)|_U ≅ Proj S(U)`. If proving
a thin, locally directed variant of the gluing directly is cheaper, the gluing
article's note allows it as a helper.

To record on this leaf once proved: the glued sheaf, its restriction isomorphisms,
invertibility, and `Hartshorne.QuasiCoherentGradedAlgebra.twistTransition`,
`Hartshorne.QuasiCoherentGradedAlgebra.twistTransitionHom_comp`,
`Hartshorne.QuasiCoherentGradedAlgebra.twistTransitionHom_id`,
`Hartshorne.QuasiCoherentGradedAlgebra.isInvertible_twistingSheaf`.

## Split proposal (resolved by the roadmap revision)

The Roadmap return proposed splitting off two articles. The roadmap revision added
them, with these differences from the proposal:

1. "Gluing sheaves of modules along open immersions"
   (`schemes/coherent-sheaves/module-gluing.md`, `af_cc5b776dbee778ca137f2f01`,
   theorem, `origin: bridged` from Exercise II.1.22, p. 69). It is stated in
   Hartshorne's open-cover form for a ringed space (`φ_ij` on `U_ij`, `φ_ii = id`,
   `φ_ik = φ_jk ∘ φ_ij` on `U_ijk`), not in the proposed thin-category form, so that it
   also serves the Picard and ideal-sheaf consumers. Depends on Gluing sheaves on an
   open cover and Sheaves of modules. It is linked from this leaf's "Depends on" and
   from the "Proof depends on" of `cohomology/cohomology-exercises/picard-h1-units.md`.
   `schemes/coherent-sheaves/module-ideal-sheaf-data.md` lists it under "Informally uses"
   only: ideal subsheaves of the structure sheaf can be glued directly, and a proof edge
   would hold that article, which lies on the coherent-extension chain, until the module
   gluing is formalized.
2. "Twisting sheaves under localization in degree zero"
   (`schemes/projective-geometry/relative-proj-bundles/proj-twist-localization.md`,
   `af_71347b8169aa158ac22ab154`, theorem, `origin: bridged`, sources Hartshorne II.7
   pp. 160–161 and Stacks 01NM). Depends on Twisting sheaves are invertible and The
   partial Proj morphism of a graded map; Proof depends on Relative Proj (for
   `isOpenImmersion_projMap`). It replaced this leaf's unlinked "Proof depends on"
   bullet. `schemes/projective-sheaves/proj-twist-pullback.md` is unchanged; the new
   article's prose and note record the relation.
3. This leaf's statement is unchanged.
