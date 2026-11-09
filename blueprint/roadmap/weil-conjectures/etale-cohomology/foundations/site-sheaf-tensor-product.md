---
article_id: af_4a270209c8460746b8d4cd54
declaration: def
origin: bridged
statement: retracted
lean: Hartshorne.sheafTensor Hartshorne.sheafTensorMap Hartshorne.sheafTensorMonoidal Hartshorne.sheafTensorSymmetric Hartshorne.sheafTensorUnit_eq Hartshorne.sheafTensorIsoTensor Hartshorne.sheafTensorIsoTensor_hom_tmul Hartshorne.AbSheaf.associator_hom_tmulSection Hartshorne.AbSheaf.leftUnitor_hom_tmulSection Hartshorne.AbSheaf.rightUnitor_hom_tmulSection Hartshorne.AbSheaf.braiding_hom_tmulSection Hartshorne.sheafificationBraided Hartshorne.sheafTensorPowSucc Hartshorne.sheafTensorPowSuccFunctor Hartshorne.sheafTensorPowSuccAddIso Hartshorne.abSheafW_isMonoidal_of_essentiallySmall Hartshorne.abSheafW_isMonoidal_of_isCoverDense AlgebraicGeometry.Scheme.etaleW_isMonoidal
---

# Tensor products of abelian sheaves on a site

Let $(\mathcal C,J)$ be a site that is essentially small, or that has an essentially small dense subsite whose sheaf category is equivalent to that of $(\mathcal C,J)$; then presheaves of abelian groups on it have associated sheaves.
For abelian sheaves $F$ and $G$ on it, define $F\otimes G$ as the sheaf associated to the
presheaf

$U\longmapsto F(U)\otimes_{\mathbb Z}G(U)$,

whose restriction maps are the tensor products of those of $F$ and $G$.  It is functorial in
both variables.

With unit the constant sheaf $\underline{\mathbb Z}$, the sheaf associated to the constant
presheaf $\mathbb Z$, this tensor product makes the category of abelian sheaves on
$(\mathcal C,J)$ a symmetric monoidal category.  That is, there are isomorphisms

$(F\otimes G)\otimes H\cong F\otimes(G\otimes H)$,
$\underline{\mathbb Z}\otimes F\cong F\cong F\otimes\underline{\mathbb Z}$, and
$F\otimes G\cong G\otimes F$,

natural in every variable and satisfying the pentagon, triangle and hexagon axioms.  On local
sections they send $(f\otimes g)\otimes h$ to $f\otimes(g\otimes h)$, $a\otimes f$ and
$f\otimes a$ to $af$ for an integer $a$, and $f\otimes g$ to $g\otimes f$.  Sheafification, from presheaves with
the sectionwise tensor product to sheaves with $\otimes$, is a symmetric monoidal functor.

Tensor powers are $F^{\otimes 1}=F$ and $F^{\otimes(k+1)}=F^{\otimes k}\otimes F$ for $k\ge 1$.
They are functorial in $F$, and the associativity isomorphisms give
$F^{\otimes a}\otimes F^{\otimes b}\cong F^{\otimes(a+b)}$ for $a,b\ge 1$.

This applies to the small étale site of a scheme $X$.  That site is not small, but its abelian
presheaves have associated sheaves and the monoidal structure exists, because the affine
schemes étale over $X$ form an essentially small subsite that is dense for the covering
families.

## Depends on

- [Associated sheaves](../../../schemes/sheaves/associated-sheaf.md)
- [The small étale site](small-etale-site.md)

## Proof depends on

- The sectionwise tensor product makes presheaves of abelian groups on $\mathcal C$ a
  symmetric monoidal category.
- If $G$ is a sheaf, the internal Hom presheaf from any abelian presheaf to $G$ is a sheaf.
  Hence tensoring with a fixed presheaf preserves the morphisms that sheafification inverts.
- A symmetric monoidal structure descends along a localization at a class of morphisms stable
  under tensor products.
- The property that sheafification-inverted morphisms are stable under tensor products
  transfers from a dense subsite whose sheaf categories are equivalent; for the small étale
  site use the essentially small site of affine étale $X$-schemes.

## Informally uses

- [The monoidal category of sheaves of modules](../../../schemes/modules-and-quasicoherent/module-sheaf-monoidal-category.md),
  the same construction for sheaves of $\mathcal O_X$-modules on a ringed space.

## Sources

- [Hartshorne Appendix C §3, suppressed twist in properties 3.4 and 3.8, pp.453–454](../../../../sources/hartshorne-appendix-c-3.md#properties-31-through-35-printed-p453)
- SGA 4, Exposé IV (operations on sheaves); Milne, *Étale Cohomology*, Chapter II.
