---
article_id: af_f569e5ff0fa1a70bd43181a6
declaration: theorem
origin: cited
source_units: [appendix-a-section-3]
---

# Symmetric expressions in formal Chern roots descend to Chern classes

After an injective splitting pullback, write

`c_t(E)=product_i(1+a_i*t)`.

Any polynomial expression symmetric in the formal symbols `a_i` is a unique
polynomial in their elementary symmetric functions, hence in the pulled-back
Chern classes of `E`.  Injectivity of Chow pullback makes the resulting class
on `X` independent of the splitting space.  For two bundles, use expressions
symmetric separately in the two root families.

The `a_i` are formal symbols; the statement does not adjoin actual roots to
the original Chow ring.

## Depends on

- [The Chow splitting principle](chow-splitting-principle.md)
- [Chern classes of a filtered bundle](filtered-bundle-chern-product.md)

## Proof depends on

- The fundamental theorem of symmetric polynomials.  The pinned declaration
  `MvPolynomial.esymmAlgHom_surjective` is supporting algebra, not a complete
  Chern-class theorem.

## Sources

- [Hartshorne Appendix A §3, formal-root discussion, pp.430–431](../../../sources/hartshorne-appendix-a-3.md)
- Hirzebruch, Chapter I, section 4.4.
