# Étale Tate twists

## Status

Not recorded. A bounded attempt built every object the article asks for: `μ_n`,
`ℤ/ℓ^r(1) = μ_{ℓ^r}`, tensor products and internal Homs of abelian étale sheaves, the twists
`ℤ/ℓ^r(q)` for every integer `q`, their inverse systems `ℤ_ℓ(q)`, and the twisted `ℤ_ℓ`- and
`ℚ_ℓ`-cohomology. Three of the ingredients are definitions the size of an article that other
articles will also need: the sheaf `μ_n`, the tensor product, and the internal Hom. Following the
bounded-attempt rule, the leaf is left unrecorded and a split proposal is given below. Once those
articles exist, the leaf can record the declarations listed in item 4.

## Checked Lean (module `Hartshorne.Weil.EtaleTateTwist`)

The module is sorry-free, imported by the library root, and uses only the standard axioms. It
imports `Hartshorne.Weil.RationalEllAdicCohomology` (for the `q = 0` inverse system and the
`q = 0` comparison of rational cohomology) and does not edit it.

- Representing ring: `Hartshorne.RootsOfUnityRing n = ℤ[ℤ/n]` (group ring), with
  `Hartshorne.universalRootOfUnity` and
  `Hartshorne.bijective_restrictRootsOfUnity_universalRootOfUnity`. Ring maps `ℤ[ℤ/n] → A`
  correspond to `n`-th roots of unity in `A`, for every `n`, including `n = 0`, where they are all
  units. The universe-lifted versions are `Hartshorne.rootsOfUnityRingCat`,
  `Hartshorne.universalRootOfUnityULift` and
  `Hartshorne.bijective_restrictRootsOfUnity_universalRootOfUnityULift`.
- `Hartshorne.rootsOfUnityFunctor n : CommRingCat ⥤ Ab` (`A ↦ μ_n(A)`, written additively),
  `Hartshorne.rootsOfUnityPowHom` and `Hartshorne.rootsOfUnityFunctorPow` (`ζ ↦ ζ^k` from
  `μ_{km}` to `μ_m`), and `Hartshorne.rootsOfUnityFunctorSystem ℓ` (`r ↦ μ_{ℓ^r}` with
  transitions `ζ ↦ ζ^(ℓ^(s-r))`).
- `AlgebraicGeometry.Scheme.rootsOfUnityPresheaf n = Γ ⋙ μ_n` on all schemes, and
  `rootsOfUnityPresheafRepresentableIso` (it is `Hom(-, Spec ℤ[ℤ/n])`, via
  `rootOfUnityOfHomSpec`, `bijective_rootOfUnityOfHomSpec`).
  `isSheaf_fpqcTopology_rootsOfUnityPresheaf` follows because fpqc is subcanonical, and
  `isSheaf_etaleTopology_rootsOfUnityPresheaf` because `etaleTopology_le_fpqcTopology`.
- Continuity of the forgetful functor from the small étale site to schemes: instances
  `isContinuous_etaleForget` and `isContinuous_etaleForget_comp_overForget` (plus
  `PreservesFiniteLimits` and `RepresentablyFlat` instances for `Etale.forget X`).
- `AlgebraicGeometry.Scheme.etaleRootsOfUnitySheaf X n : Sheaf X.smallEtaleTopology Ab`, the
  restriction of the big-site sheaf `rootsOfUnityEtaleBigSheaf n`. Its sections over `U` are
  definitionally `Additive (rootsOfUnity n Γ(U.left, ⊤))` (`etaleRootsOfUnitySheaf_obj_obj`).
- `AlgebraicGeometry.Scheme.etaleTateTwistOne X ℓ r := μ_{ℓ^r}` and
  `etaleTateTwistOneSystem X ℓ : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology Ab`, which is `ℤ_ℓ(1)` as an
  inverse system (obtained through `rootsOfUnityEtaleBigSystem`).
- For any site `J` with sheafification into `Ab`:
  - `Hartshorne.presheafTensor` and `Hartshorne.presheafTensorMap`: the pointwise `⊗_ℤ` of
    `Ab`-valued presheaves, with functoriality lemmas.
  - `Hartshorne.sheafTensor J F G`: the sheafification of the pointwise tensor product.
  - `Hartshorne.sheafTensorMap`, `Hartshorne.sheafTensorPowSucc J F k` (`F^{⊗(k+1)}`),
    `Hartshorne.sheafTensorPowSuccMap`, and `Hartshorne.sheafTensorPowSuccFunctor J k`.
- `AlgebraicGeometry.Scheme.etaleTateTwistNat X ℓ r q` is `ℤ/ℓ^r(q)` for `q ≥ 0`: the constant
  sheaf `ℤ/ℓ^r` at `q = 0` and `μ_{ℓ^r}^{⊗q}` for `q ≥ 1` (`etaleTateTwistNat_one`).
  `etaleTateTwistNatSystem X ℓ q` is the inverse system in `r`: for `q = 0` it is
  `constantTorsionEtaleSheafSystem`, for `q ≥ 1` it is the `q`-th tensor power of the
  `μ_{ℓ^r}` system (`etaleTateTwistNatSystem_obj`).
- `twistedTorsionEtaleCohomologySystem X ℓ q i` (`r ↦ H^i_et(X, ℤ/ℓ^r(q))`) and
  `classicalEllAdicCohomologyTwistNat X ℓ q i` (its inverse limit). At `q = 0` the latter is
  definitionally `classicalEllAdicCohomology` (`classicalEllAdicCohomologyTwistNat_zero`).

- Internal Hom (`AlgebraicGeometry.Scheme`): `EtaleHomOver F G U` (morphisms `F|_U ⟶ G|_U`).
  `small_etaleHomOver` shows these are `u`-small: a morphism is determined by its components at
  affine étale schemes over `U` (a small family via `equivSmallModel X.AffineEtale`), by cover
  density of the affine étale site and separatedness of `G`. Then `etaleHomOverRestrict` (with
  `_id`, `_comp`), `etaleHomPresheaf` (shrunk to `Ab.{u}`), `isSheaf_etaleHomPresheaf`, and
  `etaleSheafHom F G : Sheaf X.smallEtaleTopology Ab`.
- `etaleTateTwistNegOne X ℓ r = Hom(μ_{ℓ^r}, ℤ/ℓ^r)` and `etaleTateTwist X ℓ r : ℤ → Sheaf`.
  This is `etaleTateTwistNat` for `q ≥ 0` and `ℤ/ℓ^r(-1)^{⊗(-q)}` for `q < 0`
  (`etaleTateTwist_natCast`, `etaleTateTwist_neg_one`).
- Transitions of `ℤ_ℓ(-1)` (need `[NeZero ℓ]`):
  - `Hartshorne.zmodPowMulHom` (multiplication by `ℓ^(s-r)`, `ℤ/ℓ^r → ℤ/ℓ^s`) and
    `Hartshorne.zmodPowShortComplex`, which is exact with mono first map
    (`exact_zmodPowShortComplex`, `mono_zmodPowShortComplex_f`).
  - `constantTorsionEtaleSheafMul` and `exists_lift_constantTorsionEtaleSheafMul`: sections of
    `ℤ/ℓ^s` killed by `ℓ^r` come from `ℤ/ℓ^r`. The constant sheaf followed by sections is left
    exact. Also `mono_constantTorsionEtaleSheafMul_app` and `etaleTateTwistOneIncl`
    (`μ_{ℓ^r} ⊆ μ_{ℓ^s}`).
  - `Hartshorne.natTransLiftOfMono` (lift through a componentwise mono), `negTwistTransitionApp`,
    `etaleTateTwistNegOneTransition`, and `etaleTateTwistNegOneSystem`.
- `etaleTateTwistSystem X ℓ : ℤ → ℕᵒᵖ ⥤ Sheaf` (`ℤ_ℓ(q)`, `etaleTateTwistSystem_obj`),
  `ellAdicTwistCohomologySystem`, `classicalEllAdicCohomologyTwist` (`lim_r H^i(X, ℤ/ℓ^r(q))`),
  and `rationalEllAdicCohomologyTwist` (`ℚ_[ℓ] ⊗[ℤ_[ℓ]] H^i(X, ℤ_ℓ(q))` as a
  `ModuleCat ℚ_[ℓ]`, under `[Fact ℓ.Prime]`).
- `ℤ_ℓ`-module structure:
  - `Hartshorne.IsEllPowerTorsionSystem ℓ F` says `ℓ^r` kills the `r`-th stage of
    `F : ℕᵒᵖ ⥤ Ab`.
  - `Hartshorne.ellAdicStagePadicIntAction`, `ellAdicSystemPadicIntAction`,
    `ellAdicLimitPadicIntAction` and `ellAdicLimitModule` are a generic copy of the construction
    in `Hartshorne.Weil.RationalEllAdicCohomology`. That construction is specialised to the
    constant coefficients and uses a private helper, so it is copied rather than edited.
  - The torsion hypothesis comes from `etaleTateTwist_pow_nsmul_id` (`ℓ^r` kills `ℤ/ℓ^r(q)`).
    That rests on `etaleTateTwistOne_pow_nsmul_id`, `sheafTensorPowSucc_nsmul_id_eq_zero` and
    `etaleSheafHom_nsmul_id_eq_zero`, giving `ellAdicTwistCohomologySystem_pow_nsmul_id`.
  - `classicalEllAdicCohomologyTwistModule` is the resulting instance. By construction it is
    definitionally main's `classicalEllAdicCohomologyModule` at `q = 0`
    (`classicalEllAdicCohomologyTwistModule_zero`, proved by `rfl`). Likewise
    `rationalEllAdicCohomologyTwist_zero : rationalEllAdicCohomologyTwist X ℓ 0 i =
    rationalEllAdicCohomology X ℓ i` holds by `rfl`.

Except for the transition maps of negative twists, which need `ℓ ≠ 0`, no hypothesis on `ℓ` is
needed for these constructions, apart from `ℓ` prime for `ℤ_[ℓ]` and `ℚ_[ℓ]`. Invertibility of
`ℓ` on `X` enters only in theorems about them, as in constant-torsion-etale-sheaf.

## Mathlib gaps found

- Mathlib has no monoidal structure on `AddCommGrpCat`, so the tensor product above is defined by
  hand: pointwise `⊗_ℤ`, then sheafify. Associativity and symmetry are not proved.
  - An alternative route, not tried or checked: work with coefficients in `ModuleCat ℤ`, which is
    monoidal closed.
  - On that route, `GrothendieckTopology.W.transport_isMonoidal`
    (`Mathlib/CategoryTheory/Sites/Monoidal.lean`) could transport `J.W.IsMonoidal` from a
    cover-dense small subsite, such as a small model of `X.AffineEtale`. Then
    `Sheaf.monoidalCategory` would give a full monoidal structure on sheaves on `X_et`.
- Mathlib's `presheafHom` / `sheafHom` give the internal Hom only as a sheaf of types in
  `Type (u+1)`. The smallness argument and the shrinking above fill this gap.

## Remaining goal

No Lean work remains for the objects the article lists. What remains is the Roadmap step: create
articles 1–3 below and add the edges. Then the leaf can be recorded after an independent review.

## Split proposal

1. **Sheaf of roots of unity on the small étale site** (def).
   - Statement: for a scheme `X` and `n ≥ 1`, `μ_n(U) = {ζ ∈ Γ(U, 𝒪_U)^× : ζ^n = 1}` is a
     sheaf of abelian groups on `X_et`. It is representable by `Spec ℤ[t]/(t^n − 1)`, so it is
     an fpqc sheaf.
   - Source: Milne, Étale Cohomology, Ch. II (examples of sheaves); SGA 4½ (Tate twists).
     Hartshorne App. C §3 only uses it implicitly, through the suppressed twist.
   - Depends on: small-etale-site.
   - Would record: `AlgebraicGeometry.Scheme.etaleRootsOfUnitySheaf`, with
     `AlgebraicGeometry.Scheme.isSheaf_fpqcTopology_rootsOfUnityPresheaf` as supporting lemma.
     Already built.
2. **Tensor product of abelian étale sheaves** (def).
   - Statement: `F ⊗ G` is the sheafification of `U ↦ F(U) ⊗_ℤ G(U)`, functorial in both
     variables. It is associative and symmetric up to coherent isomorphism. Tensor powers
     `F^{⊗k}` are defined from it.
   - The cup-product article needs `F(a) ⊗ F(b) ≅ F(a+b)`. So this article should either use
     Mathlib's `Sheaf.monoidalCategory`, via the `ModuleCat ℤ` route under "Mathlib gaps found",
     or state and prove the associativity and symmetry isomorphisms for the hand-made tensor
     product, which are not yet in Lean.
   - Source: SGA 4 IV (operations on sheaves); Milne, Étale Cohomology, Ch. II.
   - Depends on: small-etale-site, associated-sheaf.
   - Would record: `Hartshorne.sheafTensor`, `Hartshorne.sheafTensorPowSucc` (with
     `Hartshorne.sheafTensorPowSuccFunctor`). These are built; the associativity and symmetry
     isomorphisms are not.
3. **Internal Hom and duals of abelian étale sheaves** (def).
   - Statement: for abelian sheaves `F, G` on `X_et`, `U ↦ Hom_{X_et/U}(F|_U, G|_U)` is a sheaf
     of abelian groups. Its groups are small because the affine étale site is essentially small.
     The dual of a `ℤ/ℓ^r`-sheaf `F` is `Hom(F, ℤ/ℓ^r)`.
   - Source: SGA 4 IV (operations on sheaves); Milne, Étale Cohomology, Ch. II. The topological
     analogue is schemes/sheaf-functors/sheaf-hom.
   - Depends on: small-etale-site. The internal Hom does not need the constant sheaves; only the
     dual `Hom(F, ℤ/ℓ^r)`, used by the leaf, involves constant-torsion-etale-sheaf.
   - Would record: `AlgebraicGeometry.Scheme.etaleSheafHom`. Already built.
4. The leaf etale-tate-twist then depends on 1–3 as well as its current dependencies.
   - It also needs rational-ell-adic-cohomology and ell-adic-integers-and-field as Depends on,
     because the rational twisted cohomology reuses that `ℤ_[ℓ]`-module structure and `ℚ_[ℓ]`.
   - Its
   statement could say that `ℤ/ℓ^r(-q) = ℤ/ℓ^r(-1)^{⊗q}` with `ℤ/ℓ^r(-1)` the dual of
   `ℤ/ℓ^r(1)`. It would record `AlgebraicGeometry.Scheme.etaleTateTwistOne`,
   `AlgebraicGeometry.Scheme.etaleTateTwist`, `AlgebraicGeometry.Scheme.etaleTateTwistSystem`,
   `AlgebraicGeometry.Scheme.classicalEllAdicCohomologyTwist` and
   `AlgebraicGeometry.Scheme.rationalEllAdicCohomologyTwist`. All of these are already built.

   The transition map `ℤ/ℓ^s(-1) → ℤ/ℓ^r(-1)` needs no Kummer theory. Restrict along the
   inclusion `μ_{ℓ^r} ↪ μ_{ℓ^s}`. The result lands in the `ℓ^r`-torsion `ℓ^{s-r}ℤ/ℓ^s ≅ ℤ/ℓ^r`.
   This sends the dual of a generator to the dual of a generator. Tensor powers of the
   inclusion would be wrong for `q ≥ 2`: they are off by a factor `ℓ^{(s-r)(q-1)}`. That is why
   the negative twists are defined as tensor powers of `ℤ/ℓ^r(-1)`.

Suggested clarification for the article (statement not edited): "inverse limit followed by
rationalization" should say that `ℤ_ℓ(q)` is the inverse system `(ℤ/ℓ^r(q))_r`, with cohomology
`lim_r H^i_et(X, ℤ/ℓ^r(q))`. It should also say that `ℚ_ℓ(q)`-cohomology is that limit tensored
with `ℚ_ℓ` over `ℤ_ℓ`, matching rational-ell-adic-cohomology. The literal limit sheaf of the
`ℤ/ℓ^r(q)` tensored with `ℚ` is not the standard object.
