---
article_id: af_51803195baca053563595b22
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.RegularLocal.projectiveDimension_le_ringKrullDim Hartshorne.RegularLocal.hasProjectiveDimensionLE_of_isRegularLocalRing
---

# Finitely generated modules over a regular local ring

Let $A$ be a Noetherian regular local ring. Every finitely generated
$A$-module $M$ has $\operatorname{pd}_A(M) \le \dim A$.

Indeed $\operatorname{pd}_A(k) = \dim A$ for the residue field $k$, and over a
Noetherian local ring the projective dimension of the residue field bounds
that of every finitely generated module.

## Depends on

- [Regular local rings](../../../nonsingular-varieties/regular-local-rings.md)
- [Projective-dimension bounds detected by Ext](projective-dimension-ext-criterion.md)

## Proof depends on

- [Projective dimension of the residue field](residue-field-projective-dimension.md)
- [Projective dimension over a local ring is bounded by that of the residue field](local-projective-dimension-residue-bound.md)

## Sources

- [Hartshorne III.6, Proposition 6.11A(a), printed p.237](../../../../sources/hartshorne-iii-6.md#quoted-homological-algebra-printed-pp236237):
  this is the finitely generated case of the bound there, which Hartshorne
  cites from Matsumura [2], Theorem 42, p.131.
