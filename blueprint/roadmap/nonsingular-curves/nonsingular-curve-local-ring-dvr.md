---
article_id: af_97cc916cf87b2af3b01cf56b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Variety.HasAffineOpenBasis.isDiscreteValuationRing_localRingAt_of_nonsingularAt
---

# Local rings of nonsingular curves are DVRs

Let $X$ be a curve with an affine-open basis and let $P$ be a nonsingular
point. Then the local ring $\mathcal{O}_{P,X}$ is a discrete valuation ring.

The proof is Hartshorne's short deduction. The local ring is a Noetherian
local domain; its Krull dimension is one because $X$ is a curve; and
nonsingularity means that it is regular. [Theorem I.6.2A](dvr-characterizations.md) therefore applies.
In particular, every local ring of a nonsingular curve is a discrete
valuation ring.

## Depends on

- [Curves](curve.md)
- [The function field is the fraction field of every local ring](local-ring-fraction-field.md)
- [Intrinsic nonsingularity](../nonsingular-varieties/intrinsic-nonsingularity.md)

## Proof depends on

- [Characterizations of discrete valuation rings](dvr-characterizations.md)
- [Dimension of the local ring of a variety](local-ring-dimension.md)
- [Local rings are unchanged on open neighbourhoods](../nonsingular-varieties/local-ring-open-invariance.md)

## Sources

- [Hartshorne I.6, local rings of nonsingular curve points are DVRs (p. 41)](../../sources/hartshorne.md#i6-local-structure-and-point-separation)
