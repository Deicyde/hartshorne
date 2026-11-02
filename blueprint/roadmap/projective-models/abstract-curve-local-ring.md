---
article_id: af_53c37b8474739d7a3ebebb55
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.ValuationSpace.abstractNonsingularCurveLocalRingAlgEquiv
---

# The local ring of an abstract curve

Let $X\subseteq C_K$ be an abstract nonsingular open curve and let $R\in X$.
The local ring at $R$ is canonically isomorphic to the valuation ring
represented by $R$, as a local $k$-algebra embedded in $K$.

The isomorphism commutes with both maps into $K$. Since the valuation ring
is a discrete valuation ring, it is regular; thus the abstract curve is
nonsingular at $R$.

## Depends on

- [Abstract nonsingular curves](../curve-normalization/abstract-nonsingular-curve.md)
- [Discrete valuation rings of a function field](../curve-normalization/function-field-dvrs.md)
- [The local ring at a point](../morphisms/local-ring.md)

## Proof depends on

- [Regularity near a valuation](regular-near-valuation.md)
- [The function field of an abstract nonsingular curve](../curve-normalization/valuation-space-function-field.md)
- [Residue fields of function-field DVRs](../curve-normalization/valuation-residue-field.md)

## Sources

- [Hartshorne I.6, definition of an abstract nonsingular curve (p. 42) and proof of Theorem 6.9 (p. 45)](../../sources/hartshorne.md#i6-projective-models)
