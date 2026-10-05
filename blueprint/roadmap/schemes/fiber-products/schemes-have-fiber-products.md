---
article_id: af_f1af0566371269504260bf8c
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
statement: formalized
proof: formalized
lean: Hartshorne.schemesHaveFiberProducts
---

# Fiber products of schemes exist

Every cospan of schemes has a fiber product, unique up to unique isomorphism.

Construct affine pullbacks by tensor products. Glue first across an affine cover of one factor, then the other, and finally across an affine cover of the base. Uniqueness is formal from the universal property.

## Depends on

- [Fiber products of affine schemes](affine-fiber-product.md)
- [Gluing local fiber products](glue-local-fiber-products.md)

## Proof depends on

- Hartshorne's seven-step construction; Mathlib's anonymous `HasPullbacks Scheme` instance verifies the result but cannot supply stable `lean:` metadata.

## Sources

- [Hartshorne II.3 (fiber-products-fibers-and-base-extension)](../../../sources/hartshorne-ii-3.md#fiber-products-fibers-and-base-extension)
