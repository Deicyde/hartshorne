# The bad-hyperplane incidence correspondence

## Status

Candidate (pending review): `Hartshorne.BertiniIncidence.bertini_bad_hyperplane_incidence`.

## Setting used by the Lean

`X ⊆ ℙⁿ_k` is a closed immersion `φ : X ⟶ projectiveSpaceOverScheme n (Spec k)`, with `X`
integral, `X.IsRegular`, `topologicalKrullDim X = r < n`, `k` algebraically closed. A hyperplane
`H_a = {∑ aᵢ xᵢ = 0}` is indexed by its coefficient vector `a ∈ kⁿ⁺¹`, matching the linear-system
framework (`linearSection`, `linearSystemSection`, `invertibleZeroIdeal`). The hyperplane section
`H_a ∩ X` is the scheme-theoretic preimage `(invertibleZeroIdeal _ (linearSection k n a)).comap φ`
(`hyperplaneSectionIdeal`). "H_a is bad at x" (`IsBadHyperplaneAt`) is: the support of `H_a ∩ X`
is all of `X`, or some point of `H_a ∩ X` over `x` has a non-regular local ring.

`|H| = (ℙⁿ_k)^∨` is `projectiveSpaceScheme k n = Proj k[a₀, …, aₙ]` with structure morphism
`dualProjectiveSpaceStructure`; `X × |H|` is `incidenceAmbient q n = pullback q
(dualProjectiveSpaceStructure k n)` with `q = φ ≫ projection`. A closed point `H` of `|H|` is
`[a]` when `Represents a H` (all `a_j X_l - a_l X_j` lie in its homogeneous prime). Closed points
of the ambient are exactly pairs of closed points (`incidenceAmbient_closedPoint`,
`incidenceAmbient_exists_closedPoint`).

The theorem states: for each closed `x`, `badHyperplaneSubspace φ x` has dimension `n - r` and
equals `{a | IsBadHyperplaneAt φ a x}` (so `B_x` is a linear subspace of `|H|` of dimension
`n - r - 1`); and there is `Z` closed, irreducible, of dimension `n - 1`, whose closed points `z`
are exactly those whose second component `[a]` is bad at the first component.

## Modules (all under `Hartshorne.Scheme.Differentials`)

* `BertiniBadHyperplaneIncidence`: pointwise part (`mem_badHyperplaneSubspace_iff`,
  `finrank_badHyperplaneSubspace`, `ker_stalkMap_eq_map_ker_app`,
  `germ_mem_maximalIdeal_sq_smul_top_iff`).
* `BertiniJetFrame`: `exists_jet_frame`; principal parts `(A ⊗_k A)/J²` and Nakayama give a local
  frame of first-order jets (locally, the kernel bundle of the jet evaluation).
* `BertiniIncidenceLocalEquations`: `exists_local_incidence_equations`; near a closed point the
  `K_x` are kernels of `r + 1` linear forms with regular coefficients and an invertible minor.
* `BertiniIncidenceAmbient`: the dual projective space, `Represents`, the ambient and the
  closed-point dictionary.
* `BertiniIncidenceChart`: on `V ×_k D₊(a_β)` the incidence is the zero locus of the local forms,
  homeomorphic to `Spec` of a polynomial ring over `Γ(X, V)` in `n - r - 1` variables.
* `BertiniIncidenceCorrespondence`: gluing and the main theorem.

## Route versus the book

The book: `V → 𝒪_x/𝔪_x²` is surjective, `B_x = ℙ(kernel)`, and `B` is a `ℙ^{n-r-1}`-bundle over
`X`. The Lean follows this, with the bundle made explicit through local frames (jet frame and an
invertible minor) and charts instead of a global projective bundle `P(K)`; no global kernel sheaf
is constructed. Closedness is by charts and the Jacobson property. Surjectivity of the jet map uses
Proposition II.7.3 (⇒) (`sectionsSeparateTangentVectors_of_isClosedImmersion`). The conormal
criterion (Theorem 8.17) is not used: the regular-hypersurface criterion gives "not regular at `x`
iff the local equation is in `𝔪_x²`" directly.

## Pitfalls

* `projectiveSpaceScheme k n` and `Proj 𝒮` unfold to each other only at default transparency;
  `rw` and instance search fail when mixed.
* Algebra on `Γ(projectiveSpaceScheme k n, D)` is slow; `BertiniIncidenceChart` proves its chart
  lemma for an abstract second scheme and specializes.
