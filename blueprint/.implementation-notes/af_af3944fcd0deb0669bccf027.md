# Functoriality of blowups — implementation note

Status: complete, sorry-free (standard axioms only). Module:
`Hartshorne/Scheme/BlowupFunctoriality.lean` (imported by the library root). Hartshorne II,
Corollary 7.15.

## Declarations

- `Hartshorne.QuasicoherentIdealSubsheaf.existsUnique_blowup_map`: for `f : Y ⟶ X` of Noetherian
  schemes and coherent `I` on `X`, there is a unique `g : Bl_{f⁻¹I·𝒪_Y} Y ⟶ Bl_I X` with
  `g ≫ π_X = π_Y ≫ f`.
- `Hartshorne.QuasicoherentIdealSubsheaf.isClosedImmersion_of_blowup_map`: if moreover `f` is a
  closed immersion, every such `g` (hence the unique one) is a closed immersion. Stated for any `g`
  over `f` rather than for a chosen `def`, so no choice-defined map is introduced.
- `Hartshorne.QuasicoherentIdealSubsheaf.isCoherent_inverseImage`: on a Noetherian `Y` the inverse
  image ideal sheaf is coherent (from `SerreAffineness.isCoherent_toModules`), so the book's
  blowup of `Y` along `f⁻¹I·𝒪_Y` needs no extra coherence hypothesis.
- `Hartshorne.reesMap_surjective_of_surjective`: a surjection `φ : R → S` induces a surjection of
  Rees algebras `R[It] → S[(IS)t]` (the "surjection from the restricted Rees algebra of `I` to the
  Rees algebra of the inverse-image ideal" of the article's proof dependencies, on affine charts).

## Route

- Existence and uniqueness follow the book: the inverse image of `I` under `π_Y ≫ f` equals the
  exceptional ideal of `Ỹ` (`IdealSheafData.comap_comp`), which is invertible by Prop. 7.13(a)
  (`isInvertible_exceptionalIdealSheaf`); then Prop. 7.14 (`existsUnique_blowup_lift`).
- Closed immersion: the book argues globally (the Rees algebra of `J` on `Y` is a quotient of the
  pullback of the Rees algebra of `I`, so `Ỹ ⟶ X̃ ×_X Y` is a closed immersion of relative Projs).
  The Lean does the same chartwise, since the relative Proj here is glued from affine pieces and
  there is no pullback-of-graded-algebra API. Being a closed immersion is local on the target
  (`IsZariskiLocalAtTarget.of_openCover` with the gluing cover of `X̃` by `Proj S(U)`). For affine
  `U ⊆ X` and `V = f⁻¹U` (affine, `Γ(U) → Γ(V)` surjective since `f` is a closed immersion,
  `Γ(V, J) = Γ(U, I) Γ(V)` by `inverseImageIdeal_ideal`), the Rees map is a graded surjection, so
  `Proj T(V) ⟶ Proj S(U)` is a closed immersion (Ex. II.3.12(a),
  `isClosedImmersion_projPartialMap_comp_top_of_surjective`, converted to `Proj.map` by
  `ProjTruncation.topIso_inv_homOfLE_projPartialMap`). Uniqueness in Prop. 7.14
  (`ReesAlgebraSheaf.hom_ext_of_isLocallyPrincipalNonZeroDivisor`, with local principality pulled
  back along the open immersion `Proj T(V) ⟶ Ỹ`) shows the square with `g` commutes, and pasting
  with `Proj T(V) = V ×_Y Ỹ`, `V = U ×_X Y`, `Proj S(U) = U ×_X X̃` (`isPullback_projι`,
  `isPullback_morphismRestrict`) shows it is a pullback, so the pullback of `g` along
  `Proj S(U) ⟶ X̃` is the closed immersion above.

## Friction

- `set` for the two Rees algebra sheaves duplicated `g` in the context and broke later rewrites;
  the proof writes `I.reesAlgebra` and `(I.inverseImage f).reesAlgebra` out in full.
- The `IsOpenImmersion` instance for `projι` was not found while unifying a hypothesis stated over
  `blowup` against a goal over `relProj`; restating the hypothesis over `relProjToBase` fixed it.
