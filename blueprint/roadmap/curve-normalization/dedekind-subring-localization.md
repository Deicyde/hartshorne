---
article_id: af_9d74ff504ccb56bf61fb3246
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-normalization]
---

# A DVR containing a Dedekind subring is its localization

Let `B` be a Dedekind domain of Krull dimension one embedded in its fraction
field `K`, and let `R ∈ C_K` contain `B`.  Contract the maximal ideal of
`R` to

`℘_R = 𝔪_R ∩ B`.

Then `℘_R` is a nonzero maximal ideal of `B`, and the canonical embedding of
the localization `B_{℘_R}` into `K` identifies it with `R`.  In particular,
the center map from DVRs containing `B` to maximal ideals of `B` is injective.

The localization dominates `B`, and `R` dominates that localization.  Since
`B_{℘_R}` is a valuation ring and valuation rings are maximal for domination,
the two subrings of `K` agree.  If the contraction were zero, the localization
would be all of `K`, contradicting that `R` is a nonfield DVR.

State equality of the images inside `K` as well as the induced ring
equivalence.  The image equality is what the finite-pole argument uses; the
equivalence is what Corollary 6.6 uses.

## Depends on

- [Discrete valuation rings of a function field](function-field-dvrs.md)

## Proof depends on

- [Valuation rings are maximal local subrings](../nonsingular-curves/valuation-ring-maximal-local-subring.md)
- [Localizations of a Dedekind domain are DVRs](../nonsingular-curves/dedekind-localization-dvr.md)

## Sources

- [Hartshorne I.6, proof of Lemma 6.5 (p. 41)](../../sources/hartshorne.md#i6-normalization-and-finite-poles)
