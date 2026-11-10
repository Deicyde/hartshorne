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

Also done, in the general setting (`x` a non-zero-divisor, `f` surjective, `ker f ⊆ (x)`):

- `liftPoint`: the point of `Proj T` over a point `p ⊇ ker f` of `Proj S`;
- `exists_local_preimage` and `exists_mulSection_preimage`: exactness at `𝒪(n)` on sections;
- `lift` and `lift_mulSection`.

For `ℙ^{m+1}_A`: `exists_eq_X_last_mul`, i.e. `ker(hyperplaneHom) = (x_{m+1})`.

Still missing for the degreewise sequence:

- the kernel fork, whose draft is below; it needs `haveI := mono_mulSection hx n hinj`, and was
  last seen failing only for that instance;
- that `psi` is an epimorphism, for example by `epi_of_stalk_surjective`
  (`Scheme/GloballyGenerated.lean`). At `p ∉ H` the stalk of the closed pushforward is zero. At
  `p ∈ H`, lift a local fraction `b̄/ḡ` on `Proj T` to `b/g` with homogeneous preimages
  (`ProjSurjection.exists_homogeneous_preimage`).

The graded Čech clause still needs the projective-twist-cech-complex node, so the article stays
unrecorded.

```lean
/-- **Exactness at `𝒪(n)`.** Multiplication by `x` is a kernel of `psi`. -/
def isLimitMulSection (hinj : Function.Injective (x * ·)) (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) (hfx : f x = 0) (hker : ∀ a, f a = 0 → ∃ b, a = x * b) :
    Limits.IsLimit (Limits.KernelFork.ofι (mulSection hx n) (mulSection_psi hx n f hfx)) :=
  haveI := mono_mulSection hx n hinj
  Limits.KernelFork.IsLimit.ofι' _ _ fun k hk =>
    ⟨lift hx n hinj f hf hker k hk, lift_mulSection hx n hinj f hf hker k hk⟩
```

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
