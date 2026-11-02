---
article_id: af_9320492f02cd29177eca029f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.disconnectedSpectrum_idempotents_products_tfae
---

# Connected spectra, idempotents, and products

For a commutative ring $A$, the following are equivalent:

1. $\operatorname{Spec} A$ is disconnected;
2. $1 = e_{1} + e_{2}$ for nonzero orthogonal idempotents $e_{1},e_{2}$;
3. $A$ is isomorphic to a product $A_{1} \times A_{2}$ of two nonzero rings.

Here “disconnected” means that the spectrum admits a separation
into two nonempty open-and-closed subsets. The empty spectrum of
the zero ring is therefore not disconnected, and all three clauses
are false for that ring. An idempotent gives the complementary
principal opens $D(e)$ and $D(1-e)$; complementary idempotents also
give the product decomposition. This is Hartshorne's Exercise II.2.19.

## Depends on

- [The Zariski topology on Spec](../spectrum-and-schemes/spec-zero-loci.md)

## Sources

- [Hartshorne II.2, Exercise 2.19, used in Theorem III.11.3 immediately before Zariski's Main Theorem, Corollary III.11.4](../../../sources/hartshorne-ii-2.md#exercises-212-through-219)
