---
article_id: af_cf9947a2c272af7039551cf1
declaration: def
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# Absolute Frobenius and Hartshorne's Frobenius twist

For a scheme `X` whose local rings have characteristic `p`, construct the
absolute Frobenius: it is the identity on the underlying space and raises
local sections to their `p`th powers.

For a `k`-scheme `X` in characteristic `p`, define Hartshorne's `X^p` to be
the same abstract scheme with structural morphism twisted by Frobenius on
`k`. Package absolute Frobenius as the `k`-linear morphism

`F' : X^p -> X`

and prove the displayed square with Frobenius on `Spec k`. This direction is
part of the API and must not be silently replaced by the opposite modern
relative-Frobenius convention.

## Depends on

- [Schemes over a base](../../schemes/spectrum-and-schemes/over-base.md)
- [The structure sheaf on a scheme](../../schemes/sheaves/regular-functions-sheaf.md)

## Proof depends on

- The ring Frobenius is functorial and induces local homomorphisms on local
  rings.
- Equality of sheaf morphisms may be checked on affine opens.

## Sources

- [Hartshorne IV.2, Frobenius definition and Remark 2.4.1, pp.301–302](../../../sources/hartshorne-iv-2.md#frobenius-and-purely-inseparable-maps-pp301302)
