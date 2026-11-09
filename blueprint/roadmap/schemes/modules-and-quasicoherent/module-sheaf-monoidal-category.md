---
article_id: af_c3111cf65623ed1a0bd6096a
declaration: instance
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.Ringed.monoidalCategory Hartshorne.Ringed.tensorUnit_eq Hartshorne.Ringed.moduleSheafTensorIsoTensor Hartshorne.Ringed.moduleSheafTensorIsoTensor_hom_bilinear Hartshorne.Ringed.associator_hom_tmulSection Hartshorne.Ringed.leftUnitor_hom_tmulSection Hartshorne.Ringed.rightUnitor_hom_tmulSection Hartshorne.Ringed.sheafificationFunctor_monoidal Hartshorne.Ringed.schemeModulesMonoidalCategory
---

# The monoidal category of sheaves of modules

For a ringed space $(X,\mathcal{O}_X)$, equip the category of $\mathcal{O}_X$-modules
with a monoidal category structure whose tensor product is the tensor product
$F\otimes_{\mathcal{O}_X}G$ of module sheaves and whose unit object is
$\mathcal{O}_X$.  It consists of associativity isomorphisms
$(F\otimes G)\otimes H\cong F\otimes(G\otimes H)$ and unit isomorphisms
$\mathcal{O}_X\otimes F\cong F$ and $F\otimes\mathcal{O}_X\cong F$, natural in every
variable and satisfying the pentagon and triangle axioms.  On the sections over
an open set, the associativity isomorphism sends $(f\otimes g)\otimes h$ to
$f\otimes(g\otimes h)$ and the unit isomorphisms send $a\otimes f$ and
$f\otimes a$ to $af$.  The tensor product of the structure is identified with
the sheafified tensor product of module sheaves by a canonical isomorphism
sending each section $f\otimes g$ to $f\otimes g$.

The sectionwise tensor product
makes presheaves of modules a monoidal category.  Sheafification is the
localization at the morphisms it inverts, and these morphisms are stable under
tensor products, because sheafification preserves stalks and the stalk of a
sectionwise tensor product is the tensor product of the stalks.  The monoidal
structure therefore descends to sheaves of modules, and sheafification becomes
a monoidal functor.

## Depends on

- [Tensor products of module sheaves](module-tensor-product.md)

## Proof depends on

- [Sheafification preserves stalks](../sheaves/associated-sheaf-stalks.md)
- [Isomorphisms are detected on stalks](../sheaves/stalkwise-isomorphism.md)
- The sectionwise monoidal structure on presheaves of modules.
- A monoidal structure descends along a localization at a class of morphisms
  stable under tensor products.

## Sources

- [Hartshorne II.5, tensor product definition on printed p. 109](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
