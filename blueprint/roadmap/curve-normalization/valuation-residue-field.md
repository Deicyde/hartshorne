---
article_id: af_6ae7ab997d79403ec249423a
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.FunctionFieldDVR.residueAt
---

# Residue fields of function-field DVRs

Let $k$ be algebraically closed, let $K/k$ be a finitely generated field
extension of transcendence degree one, and let $R\in C_K$. The natural map

$$k\longrightarrow\kappa(R)=R/\mathfrak m_R$$

is an isomorphism. Composing the quotient map with its inverse gives the
canonical residue evaluation $R\to k$, which fixes constants.

[Hartshorne's Corollary I.6.6](dvr-affine-model.md) realizes $R$ as the local
ring of a $k$-rational point $P$ on a nonsingular affine curve. Evaluation
at $P$ identifies its residue field with $k$. Transporting that identification
through the compatible local-ring isomorphism gives the residue evaluation
on $R$. The residue of a transported germ equals its value at $P$.

## Depends on

- [Discrete valuation rings of a function field](function-field-dvrs.md)

## Proof depends on

- [Every function-field DVR has a nonsingular affine model](dvr-affine-model.md)
- [The local ring is local](../morphisms/local-ring-is-local.md)

## Sources

- [Hartshorne I.6, residue fields of points of $C _K$ (p. 42)](../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
