# The hyperplane exact-sequence bridge

## Status: degreewise sequence formalized (w30l); not recorded; Roadmap return stands

`src/Hartshorne/Scheme/ProjectiveHyperplaneSequence.lean` (not imported by the library root)
proves, for a surjective graded map `f : S → T` and a non-zero-divisor `x ∈ S_1` with
`ker f = (x)`, that `0 → 𝒪(n-1) → 𝒪(n) → f_* 𝒪_{Proj T}(n) → 0` is short exact
(`Hartshorne.HyperplaneSequence.shortExact`). The first map is multiplication by `x`
(`mulSection`); the second is `ProjTwistPullback.psi`.

For `ℙ^{m+1}_A` with `H = V₊(x_{m+1}) ≅ ℙ^m_A` this is
`Hartshorne.HyperplaneSequence.hyperplane_shortExact`. It uses `hyperplaneHom`
(`x_{m+1} ↦ 0`), `isClosedImmersion_hyperplane` and `exists_eq_X_last_mul`
(`ker = (x_{m+1})`). Axioms are standard and the unusedArguments lint is clean.

The article is still not recordable, for the reasons below. The `⊕_n` form and the cohomology
clause are missing. The target sheaf is `f_*(𝒪_{Proj T}(n)|_U)` with `U = projPartialDomain f = ⊤`,
rather than a pushforward along a morphism out of `Proj T` itself. A recorded version would also
need the degreewise reading of the statement accepted, or the Roadmap change suggested below.

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

