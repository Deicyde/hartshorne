# The hyperplane exact-sequence bridge

## Status: partial Lean (w30l); not recorded; Roadmap return stands

`src/Hartshorne/Scheme/ProjectiveHyperplaneSequence.lean` (not imported by the library root)
has, for a graded map `f : S → T` and `x ∈ S_1` with `f x = 0`:

- `mulSection hx n : 𝒪(n-1) ⟶ 𝒪(n)`, multiplication by `x`, via `projGradedModuleSheafMap`;
- `mulSection_psi`: `mulSection ≫ ProjTwistPullback.psi f n = 0`;
- `mono_mulSection`: a monomorphism when `x` is a non-zero-divisor.

For `ℙ^{m+1}_A`: `hyperplaneHom` (`x_{m+1} ↦ 0`, graded and surjective),
`isClosedImmersion_hyperplane`, `mulSection_psi_hyperplane` and
`mono_mulSection_hyperplane`.

Still missing for the degreewise sequence: exactness at `𝒪(n)` (every local section killed by
`psi` is `x` times a section) and that `psi` is an epimorphism (stalks of the closed
pushforward). The route planned for exactness at `𝒪(n)` is pointwise. Since `x·` is injective on
fibers, the preimage can be defined pointwise. It is locally a fraction:

- off `H`: `m/g = x m/(x g)`;
- on `H`: from `psi t = 0`, take `u ∉ p` homogeneous with `u m ∈ ker f = (x)`.

This needs the point of `Proj T` over a point `p ⊇ ker f` of `Proj S`.

## Why it is returned

- **Missing dependency for the cohomology clause.** The statement includes "the resulting
  cohomology map is multiplication by `x_r` under the graded Čech identifications". Those
  identifications are the content of the standard graded Čech complex node
  (projective-twist-cech-complex). That node is not a dependency of this article and is not yet
  formalized. Either add the edge, or move the cohomology clause to the node that uses it
  (projective-space-intermediate-twist-vanishing, which already depends on both).
- **Graded direct sums.** The sequence is stated for `⊕_n 𝒪_X(n)`, an infinite direct sum of
  module sheaves. The project has no coproduct of module sheaves over `ℤ` with its
  quasi-coherence or cohomology API in the DAG. The degreewise sequence
  `0 → 𝒪_X(n-1) → 𝒪_X(n) → i_* 𝒪_H(n) → 0`, one `n` at a time, would avoid this.

## Available ingredients for the degreewise sequence

- The closed immersion `H = Proj S/(x_r) → Proj S`, from the surjection `S → S/(x_r)`:
  `Hartshorne.isClosedImmersion_projPartialMap_of_surjective` and
  `projPartialDomain_eq_top_of_surjective` (Scheme/ProjSurjectionClosedImmersion.lean).
- The map `𝒪_{Proj S}(n) → f_*(𝒪_{Proj T}(n)|_U)` for a graded map `S → T`, together with
  `f^* 𝒪_S(n) ≅ 𝒪_T(n)|_U` and the pushforward formula: `Hartshorne.ProjTwistPullback.psi`,
  `pullbackTwistIso` and `pushforwardTwistIso` (Scheme/ProjTwistPullback.lean). With
  `T = S/(x_r)`, `U` is all of `Proj T`, and `psi` is the restriction map
  `𝒪_X(n) → i_* 𝒪_H(n)`.
- Multiplication by the degree-one section `x_r`, `𝒪_X(n-1) → 𝒪_X(n)`: use `degreeOneSection`
  (Scheme/GloballyGenerated.lean) together with `twistMulIso` (Scheme/ProjTwistCompatibility.lean).

## Suggested route for the degreewise sequence

Check exactness on stalks, or on the charts `D_+(x_j)`, where the sequence is
`0 → S(n-1)_(x_j) → S(n)_(x_j) → (S/x_r)(n)_(x_j) → 0`. This is the degree-zero part of the
localization of `0 → S(-1) → S → S/(x_r) → 0`, shifted by `n`. It is exact because `x_r` is a
non-zero-divisor and homogeneous localization is exact.
