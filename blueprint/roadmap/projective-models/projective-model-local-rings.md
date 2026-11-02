---
article_id: af_23b2537cc3ff2433010bec6d
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.projectiveDiagonal_localRingRange_eq
---

# Local rings of the diagonal model

For the diagonal model $\varphi:C_K\to Y$ and every point $P\in C_K$,
the induced map identifies the image of $\mathcal O_{\varphi(P),Y}$ in
the common function field $K$ with the valuation ring represented by $P$.

The comparison is Hartshorne's sequence of inclusions inside $K$:

$$\mathcal O_{\varphi_i(P),Y_i}\subseteq
\mathcal O_{\varphi(P),Y}\subseteq\mathcal O_{P,C_K}.$$

On a chart the outer composite is an isomorphism, so both inclusions are
equalities. In particular, each induced local-ring map is bijective,
as required by the local isomorphism criterion. All comparisons use the
same function-field identification and projection identities as the
diagonal function-field theorem.

## Depends on

- [The projective diagonal model](projective-diagonal.md)
- [The local ring is functorial](../morphisms/local-ring-functorial.md)
- [The function field of the diagonal model](projective-model-function-field.md)

## Proof depends on

- [The local ring of an abstract curve](abstract-curve-local-ring.md)
- [Dense morphisms inject on local rings](dominant-morphism-local-ring.md)
- [A two-chart affine cover of the valuation curve](two-affine-chart-cover.md)
- [Local rings are unchanged on open neighbourhoods](../nonsingular-varieties/local-ring-open-invariance.md)

## Sources

- [Hartshorne I.6, local-ring sandwich in the proof of Theorem 6.9 (p. 45)](../../sources/hartshorne.md#i6-projective-models)
