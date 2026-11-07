# The sheaf of roots of unity on the small étale site

## Status

Added by a roadmap revision that splits the etale-tate-twist leaf. The Lean below already exists
in the sorry-free module `Hartshorne.Weil.EtaleTateTwist` (imported by the library root, standard
axioms only), built by the bounded attempt on etale-tate-twist. Nothing is recorded in the
frontmatter, so that a later Formalize pass records it after independent review.

## Candidate declarations

Main target (namespace `AlgebraicGeometry.Scheme`):

- `AlgebraicGeometry.Scheme.etaleRootsOfUnitySheaf X n : Sheaf X.smallEtaleTopology Ab`, the
  restriction of the big-site sheaf `rootsOfUnityEtaleBigSheaf n` along the continuous forgetful
  functor `Etale.forget X ⋙ Over.forget X`. Its sections over `U` are definitionally
  `Additive (rootsOfUnity n Γ(U.left, ⊤))` (`etaleRootsOfUnitySheaf_obj_obj`, by `rfl`), which
  matches the article's description of `μ_n(U)` (written additively).

Supporting, backing the representability and sheaf sentences:

- `AlgebraicGeometry.Scheme.rootsOfUnityPresheaf n = Γ ⋙ rootsOfUnityFunctor n` on all schemes.
- `AlgebraicGeometry.Scheme.rootsOfUnityPresheafRepresentableIso n`: it is
  `Hom(-, Spec ℤ[ℤ/n])`, via `rootOfUnityOfHomSpec` and `bijective_rootOfUnityOfHomSpec` (a
  morphism to `Spec` is the root of unity it pulls the tautological one back to).
- `AlgebraicGeometry.Scheme.isSheaf_fpqcTopology_rootsOfUnityPresheaf` (fpqc is subcanonical:
  `GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable`),
  `etaleTopology_le_fpqcTopology`, `isSheaf_etaleTopology_rootsOfUnityPresheaf`,
  `rootsOfUnityEtaleBigSheaf`.
- Continuity of the forgetful functor: instances `isContinuous_etaleForget`,
  `isContinuous_etaleForget_comp_overForget`, plus anonymous `PreservesFiniteLimits` and
  `RepresentablyFlat` instances for `Etale.forget X`.
- Representing ring: `Hartshorne.RootsOfUnityRing n = ℤ[ℤ/n]` (the group ring
  `MonoidAlgebra ℤ (Multiplicative (ZMod n))`, isomorphic to `ℤ[t]/(t^n − 1)`; the Lean never
  writes the quotient presentation, the reviewer should accept the group ring as the article's
  `ℤ[t]/(t^n-1)` or ask for the comparison), `Hartshorne.universalRootOfUnity`,
  `Hartshorne.bijective_restrictRootsOfUnity_universalRootOfUnity`, and the universe-lifted
  `Hartshorne.rootsOfUnityRingCat`, `Hartshorne.universalRootOfUnityULift`,
  `Hartshorne.bijective_restrictRootsOfUnity_universalRootOfUnityULift`.
- Functor on rings: `Hartshorne.rootsOfUnityFunctor n : CommRingCat ⥤ Ab`.
- The last paragraph (inclusion and power maps, `m ∣ n`):
  `AlgebraicGeometry.Scheme.etaleRootsOfUnitySheafMap X α` turns a natural transformation
  `α : rootsOfUnityFunctor m ⟶ rootsOfUnityFunctor n` into a sheaf morphism `μ_m ⟶ μ_n`. Use it
  with `Hartshorne.rootsOfUnityFunctorIncl h` (`m ∣ n`, the inclusion) and with
  `Hartshorne.rootsOfUnityFunctorPow h` (`k * m = n`, `ζ ↦ ζ^k`, built from
  `Hartshorne.rootsOfUnityPowHom`). There is no named declaration for the power map at the
  sheaf level; the inverse system `rootsOfUnityEtaleBigSystem ℓ` / `etaleTateTwistOneSystem X ℓ`
  uses `Hartshorne.rootsOfUnityFunctorSystem ℓ` instead. Formalize may add two one-line
  abbreviations (`etaleRootsOfUnitySheafIncl`, `etaleRootsOfUnitySheafPow`) or record the
  generic map with the two functor-level transformations.

Recording suggestion: `lean: AlgebraicGeometry.Scheme.etaleRootsOfUnitySheaf
AlgebraicGeometry.Scheme.isSheaf_fpqcTopology_rootsOfUnityPresheaf
AlgebraicGeometry.Scheme.rootsOfUnityPresheafRepresentableIso
AlgebraicGeometry.Scheme.etaleRootsOfUnitySheafMap`. `declaration: def` matches the main target.

## Hypotheses

The Lean takes any `n : ℕ`; at `n = 0` it gives the sheaf of all units. The article states
`n ≥ 1`, the case used; the Lean definition is a harmless generalization. No hypothesis on `X`
(in particular no invertibility of `n`) is needed.

## Library search

The pinned Mathlib has no roots-of-unity sheaf (`grep rootsOfUnity` in
`Mathlib/AlgebraicGeometry` and `Mathlib/CategoryTheory` is empty). It has the fpqc topology
(`Mathlib/AlgebraicGeometry/Sites/Fpqc.lean`), its subcanonicity, and
`etaleTopology_le_proetaleTopology`, `proetaleTopology_le_fpqcTopology`. `autoform search` for
"roots unity", "fpqc", "subcanonical" found no existing article.
