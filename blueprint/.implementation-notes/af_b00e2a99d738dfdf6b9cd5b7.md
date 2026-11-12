# Blowing up a variety

## Lean

Module `Hartshorne.Scheme.BlowupVariety`.

- `Hartshorne.QuasicoherentIdealSubsheaf.blowup_variety`: the proposition. Conventions:
  - a variety over `k` is an integral scheme `X` with a separated morphism
    `p : X ⟶ Spec k` of finite type (`FiniteType p`); `k` is any field (the book takes `k`
    algebraically closed, which the proof never uses); `IsNoetherian X` is derived inside the
    statement from `finiteType_isNoetherian p hp`;
  - `I` nonzero means some section `I.ideal U` is a nonzero ideal;
  - birational means `π ∣_ U` is an isomorphism for some nonempty open `U ⊆ X` (the witness is
    the complement of the center, `centerCompl`);
  - quasi-projective / projective over `k` means `QuasiProjective p` / `Projective p`.
- `Hartshorne.QuasicoherentIdealSubsheaf.isIntegral_blowup`: the blowing-up of an integral
  Noetherian scheme along a coherent ideal with a nonzero section is integral.

Helpers in the same module (not recorded elsewhere):

- `Hartshorne.irreducibleSpace_proj_of_isDomain`, `isDomain_stalk_proj_of_isDomain`,
  `isIntegral_proj_of_isDomain`: `Proj A` of a graded domain is integral when nonempty (the zero
  ideal is a relevant prime and the generic point; stalks embed in localizations of `A`).
- `Hartshorne.Projective.comp_quasiProjective`: projective followed by quasi-projective is
  quasi-projective when the composite is quasi-compact (factor the immersion
  `X ⟶ ℙʳ_Y ⊆ ℙʳ_W` through its scheme-theoretic image).
- `Hartshorne.QuasiProjective.exists_isAmple`: quasi-projective and finite type over a
  Noetherian ring gives an ample sheaf (the restriction of `𝒪(1)` is very ample, then the
  very-ample-power theorem with `m = 1`).
- `Hartshorne.QuasiCoherentGradedAlgebra.exists_projι_eq`, `exists_projι_eq_of_mem`: every
  point of `Proj_X S` lies in an affine piece `Proj S(U)`.
- `isDomain_reesAlgebra_obj`, `nonempty_centerCompl`,
  `exists_blowupProjection_eq_of_mem_centerCompl`.

## Route

Integrality: each affine piece `Proj (⨁_d Γ(U, I)ᵈ tᵈ)` is the `Proj` of a subring of
`Γ(U, 𝒪_X)[t]`, a domain, so it is integral when nonempty; hence the blowing-up is reduced
(stalks are domains). `π⁻¹(X \ Y) ≅ X \ Y` is irreducible, and it meets every affine piece
through a point (since `X \ Y` meets every nonempty affine open of the irreducible `X`, and `π`
is surjective over `X \ Y`), so it is dense and the blowing-up is irreducible.
Surjectivity: the image of `π` is closed (proper) and contains the dense open `X \ Y`.
Projectivity: an ample sheaf on quasi-projective `X` makes the relative `Proj` projective
(Proposition 7.10(b)); then compose.
