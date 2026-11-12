# The projective-normality criterion

## Lean

Module `Hartshorne.Scheme.ProjectiveNormalityCriterion`.

- `Hartshorne.ProjectiveNormality.IsProjectivelyNormal ℐ`: for a quasi-coherent ideal sheaf `ℐ`
  on `ℙʳ_k = Proj k[x₀, …, xᵣ]` (the ideal sheaf of a closed subscheme `X`), the homogeneous
  coordinate ring `S/Γ_*(ℐ)` (`ProjectiveClosedSubscheme.gammaStarIdeal`) is a domain and
  integrally closed. This is the book's definition (Ex. 5.14, with `S(X) = S/Γ_*(I_X)`).
- `Hartshorne.ProjectiveNormality.restrictTwist I n`: the restriction map
  `Γ(ℙʳ, 𝒪(n)) → Γ(Proj (S/I), 𝒪(n))`, global sections of `ProjTwistMap.twistHom` for the graded
  quotient map `S → S/I` (so `𝒪_X(n)` is the twisting sheaf of `Proj (S/I)`, identified with the
  pullback of `𝒪(n)` as in Prop. 5.12(c)).
- `Hartshorne.ProjectiveNormality.isProjectivelyNormal_iff`: the criterion, for `X` the closed
  subscheme `Proj (S/Γ_*(ℐ))` (Cor. 5.16), under `[ConnectedSpace X]` and `[IsAlgClosed k]`.
- `Hartshorne.ProjectiveNormality.isDomain_and_isIntegrallyClosed_iff`: the same for a saturated
  homogeneous ideal `I` (same hypothesis shape as Ex. 5.14(a)'s
  `projectiveSectionRing_isIntegralClosure`).

## Hypotheses

Connectedness is the standing hypothesis of Hartshorne's Exercise 5.14 (and of the Ex. 5.14(a)
theorem used). The article omits it; without it (or at least nonemptiness) the statement fails
for the empty subscheme: `ℐ = 𝒪`, `S(X) = 0` is not a domain, while `X = ∅` is normal and the
restriction maps are surjective. With nonemptiness only, `(⇒)` gets connectedness from
irreducibility (the generic point `(0)` of a domain lies in every nonempty open), and `(⇐)` from
surjectivity in degree `0` (an idempotent section `1` on one clopen piece, `0` on the other, is
not the restriction of a constant); this strengthening is not formalized.

The algebraic closedness of `k` is used only through the Ex. 5.14(a) theorem, which keeps it as
the book's setting.

## Route

The book's: (a) gives `S' = ⨁_{n ≥ 0} Γ(X, 𝒪_X(n))` as the integral closure of `S/I` in `K`
(values at the generic point, `sectionRingToFraction`). The restriction of a form `b ∈ S_n`
(every section of `𝒪_{ℙʳ}(n)` is one, Prop. 5.13 via
`ProjectiveClosedSubscheme.exists_mem_sectionRingMap_eq`) has value `b̄` in `K`
(`sectionValue_restrictTwist_polySection`). Normality from integral closedness goes through the
charts: `isIntegrallyClosed_away_of_isIntegrallyClosed` shows `A_(f)` integrally closed for an
integrally closed graded domain `A` and `f ∈ A₁ \ 0` (an element of `Frac A_(f)` integral over
`A_(f)` is integral over `A_f`, hence in `A_f`, and its degree-zero part is itself, by
`algebraMap_decompose_eq`); stalks are localizations of chart rings.

## Friction

`obtain ⟨x, hx⟩ := <term>` on terms whose type mentions the twisting-sheaf sections over
`Proj (S/I)` can take several seconds (and `obtain ⟨t', rfl⟩` exceeded the heartbeat budget);
binding the term with `have` first and then destructuring is fast. Rewriting with
`(sectionRingToFraction 𝒬).map_add` or closing `algebraMap (s + s') = … + …` goals hit `isDefEq`
timeouts (two `+` instance paths on `FractionRing`); membership in `(algebraMap S K).range` with
`add_mem` avoids it.
