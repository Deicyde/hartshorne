---
article_id: af_bf9a7cd3954a8ae39f1a8b34
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.torsionEtaleCohomologySystem AlgebraicGeometry.Scheme.classicalEllAdicCohomology
---

# The classical inverse system of torsion étale cohomology

For fixed $i$, the reduction morphisms of coefficient sheaves define an
inverse system

$\ldots \to H^i_{\mathrm{et}}(X,\mathbb{Z}/\ell ^{r+1}\mathbb{Z}) \to H^i_{\mathrm{et}}(X,\mathbb{Z}/\ell ^r\mathbb{Z}) \to \ldots$.

Define the classical integral ℓ-adic group by the ordinary inverse limit

$H^i_{\mathrm{classical}}(X,\mathbb Z_\ell)=\varprojlim_r H^i_{\mathrm{et}}(X,\mathbb{Z}/\ell^r\mathbb{Z})$.

This definition records, rather than suppresses, the later obligation to
compare ordinary inverse limits with derived limits.  No automatic
surjectivity or Mittag–Leffler assertion is made here.

## Depends on

- [Torsion étale cohomology](torsion-etale-cohomology.md)
- [The ℓ-adic integers](ell-adic-integers-and-field.md)

## Proof depends on

- Categorical inverse limits in abelian groups.  Exactness and
  Mittag–Leffler enter only in later comparison theorems, not in this
  definition.

## Sources

- [Hartshorne Appendix C §3, inverse-limit definition, p.453](../../../../sources/hartshorne-appendix-c-3.md#definition-and-coefficients-printed-p453)
