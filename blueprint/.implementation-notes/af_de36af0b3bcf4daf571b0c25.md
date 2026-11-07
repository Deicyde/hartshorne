# The relative twisting sheaf

## Status

Not recorded: the statement needs the gluing of sheaves of modules along the affine
pieces of the relative Proj, which neither the pinned Mathlib nor the project has
(Mathlib defines `Pseudofunctor.IsStack` but proves no stack instance for
`SheafOfModules`; the project's Exercise II.1.22 gluing handles sheaves valued in a
fixed category only). Every other ingredient is now built, sorry-free, in two
modules imported by the library root.

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
  `isIso_twistRestrictHom`, `twistRestrictIso`. This is the article's unlinked
  "Proof depends on" bullet (twisting sheaves under localization on degree zero).

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

A gluing theorem for sheaves of modules (proposed below). Applied to
`F = S.projFunctor`, `ι = S.projι`, `M U = twistingSheaf S 1 U`, `θ = twistTransition`
it yields `𝒪_{Proj_X S}(1)` with `(projι U)^* 𝒪(1) ≅ twistingSheaf S 1 U`.
Invertibility is local: transport `isInvertible_twistingSheaf` along these
isomorphisms (the `projι U` cover `relProj`). The compatibility over an affine open
`U ⊆ X` is the gluing isomorphism composed with `restrictIso`, via
`restrictFunctorComp` along `(Proj_X S)|_U ≅ Proj S(U)`.

## Split proposal (Roadmap return)

1. New article "Gluing sheaves of modules along open immersions" (theorem): for a
   scheme `Y`, a thin index category `I`, a functor `F : I ⥤ Sch` with open
   immersions `ι_i : F(i) → Y` compatible with `F`, jointly surjective and locally
   directed (a point of `ι_i(F i) ∩ ι_j(F j)` lies in `ι_k(F k)` for some `k → i`,
   `k → j`), `𝒪_{F(i)}`-modules `M_i` and isomorphisms `θ_f : (F f)^* M_j ≅ M_i`
   satisfying the identity and cocycle conditions, there is an `𝒪_Y`-module `M` with
   isomorphisms `ι_i^* M ≅ M_i` compatible with the `θ_f`, unique up to unique
   isomorphism. Source: Hartshorne II, Exercise 1.22 (p. 69), module version.
   Depends on: Gluing sheaves on an open cover
   (`schemes/sheaf-functors/gluing-sheaves.md`), Sheaves of modules. No Lean yet.
   Suggested route: `M = lim_{i ∈ Iᵒᵖ} (ι_i)_* M_i` in `Y.Modules` (limits exist and
   are sectionwise; the transition maps come from `θ_f` through
   `restrictAdjunction`); show `ι_i^* M ⟶ M_i` is an isomorphism on sections using
   local directedness and the sheaf property of each `M_j`.
2. New article "Twisting sheaves under localization on degree zero" (theorem): for
   `B = A[1/s]` with `s ∈ A₀`, `𝒪_{Proj A}(n)|_{Proj B} ≅ 𝒪_{Proj B}(n)`, functorial
   in composites of such localizations. Source: Hartshorne II.7 pp. 160–161 (used
   implicitly in the relative Proj construction); Stacks 01NM. Depends on: Twisting
   sheaves are invertible, Relative Proj. Records
   `Hartshorne.ProjTwistMap.twistFiber_comp`, `Hartshorne.ProjTwistMap.twistRestrictHom`,
   `Hartshorne.ProjTwistMap.isIso_twistRestrictHom`,
   `Hartshorne.ProjTwistMap.twistRestrictIso`.
3. Edges: this leaf Depends on (1) and Proof-depends on (2), replacing the unlinked
   bullet. The leaf would then record the glued sheaf, its restriction isomorphisms,
   invertibility, and `Hartshorne.QuasiCoherentGradedAlgebra.twistTransition`,
   `twistTransitionHom_comp`, `twistTransitionHom_id`, `isInvertible_twistingSheaf`.
