---
article_id: af_e9d7f73eeb81be8dbd2f558c
declaration: isomorphism
origin: bridged
---

# Normal birational targets recover the structure sheaf

Let $f : X \to Y$ be a birational projective morphism of Noetherian integral
schemes, with $Y$ normal. Then the canonical unit map is an isomorphism

$\mathcal{O}_Y \simeq f_* \mathcal{O}_X$.

This isolates the algebraic step in Hartshorne's proof of his connected-fibre
form of Zariski's Main Theorem.

## Depends on

- [Coherence of projective higher direct images](../../higher-direct-images/projective-higher-direct-images-coherent.md)
- [Affine opens have fraction field $K(X)$](../../../schemes/normalization-and-exercises/function-field-integral-scheme.md)
- [Normal schemes](../../../schemes/normalization-and-exercises/normal-scheme.md)

## Proof depends on

- Locally on $Y = \operatorname{Spec} A$, the algebra
  $B = \Gamma (Y, f_*\mathcal{O}_X)$ is finite over $A$.
- Birationality identifies the function fields of $X$ and $Y$, embedding the
  integral domains $A$ and $B$ in that common field; normality makes $A$
  integrally closed, so $A = B$.

## Sources

- [Hartshorne III.11, proof of Corollary 11.4, p.280](../../../../sources/hartshorne-iii-11-12.md#applications-of-formal-functions-pp279281)
