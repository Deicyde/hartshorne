# Serre's criterion for regularity

## Status

New article from the regular-localization split (roadmap revision). The
project already proves the result, sorry-free, but the article records no
declaration yet: a later Formalize pass records it after independent review.

## Candidate Lean

In the module `Hartshorne.Scheme.SerreRegularity`:

- `Hartshorne.SerreRegularity.isRegularLocalRing_of_hasProjectiveDimensionLE`:
  for `n : ℕ` and every `B` with `[CommRing B] [IsLocalRing B] [IsNoetherianRing B]`,
  `HasProjectiveDimensionLE (ModuleCat.of B (ResidueField B)) n → IsRegularLocalRing B`.
  This is the article statement ("finite projective dimension" as a bound by
  some `n`).

Helpers in the same module: `isRegularLocalRing_of_maximalIdeal_eq_bot`,
`maximalIdeal_eq_bot_of_projective`,
`exists_surjective_ker_le_maximalIdeal_smul`,
`projective_of_mem_associatedPrimes`, `mem_span_singleton_smul_top_iff`,
`projective_quotient_smul_top`, `hasProjectiveDimensionLE_quotient` (change of
rings), `nonempty_retract_residueField_quotient` (the residue field is a
direct summand of $\mathfrak m/x\mathfrak m$), and `isRegularLocalRing_of_quotient`.

The last helper is the module's own proof of the lifting statement that the
existing article regular-local-lift-from-regular-quotient records as
`Hartshorne.isRegularLocalRing_of_isRegularLocalRing_quotient_span_singleton`.
The Proof depends on edge to that article is mathematical; a Formalize pass
may either reroute the proof through the recorded declaration or accept the
duplicate helper.

## Source

Matsumura is not among the blueprint sources. The article cites Serre's
theorem as Matsumura, *Commutative Ring Theory*, Theorem 19.2, from the
supervisor's request; that number was not checked against the book. Hartshorne
does not state the criterion: it is the second half of the proof of the
localization theorem he cites in II.8, Theorem 8.14A (p.177).
