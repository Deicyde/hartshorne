# The hyperplane exact-sequence bridge

## Status: not started in Lean; Roadmap return

No Lean has been written for this node.

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
