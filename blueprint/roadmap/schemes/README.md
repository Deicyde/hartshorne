# Scheme foundations

Hartshorne Chapter II replaces embedded varieties by locally ringed spaces
glued from affine spectra. This fine milestone covers §§II.1–8 (printed
pp. 60–190): sheaves and stalks, `Spec` and `Proj`, schemes and their morphisms,
the first local and finiteness properties, subschemes, dimension, fibre
products, separatedness, properness, projective morphisms, quasi-coherent and
coherent modules, divisors, Picard groups, linear systems, projective bundles,
blowups, differentials, canonical sheaves, lci geometry, base change, and the
normalization prerequisites used later in the book.

The roadmap follows Mathlib's categorical representations rather than adding
parallel foundations. Presheaves and sheaves are functors on opens, schemes are
Mathlib `Scheme`s, schemes over a base live in a slice category, and fibre
products are categorical pullbacks. Source-shaped wrappers remain planned when
Hartshorne's exact statement is not exposed by one stable declaration.

An exercise is adopted when running text in the approved whole-book scope
cites or delegates to it, or when later running text uses it. Examples that
merely illustrate an existing construction stay in the source notes rather
than becoming artificial proof targets.

## Sheaves

- [Sheaves, stalks, and exactness](sheaves/README.md)
- [Sheaf functors, support, and gluing](sheaf-functors/README.md)

## Affine and projective schemes

- [Spectra, locally ringed spaces, and schemes](spectrum-and-schemes/README.md)
- [Projective spectra](projective-spectrum/README.md)
- [Classical varieties as schemes](variety-comparison/README.md)
- [Foundational scheme properties and exercises](foundational-properties/README.md)

## First properties

- [Local, Noetherian, and finite-type properties](first-properties/README.md)
- [Subschemes and dimension](subschemes-and-dimension/README.md)
- [Fibre products and base change](fiber-products/README.md)
- [Normalization and later-used exercises](normalization-and-exercises/README.md)

## Separated and proper morphisms

- [Separated morphisms and valuation uniqueness](separated-morphisms/README.md)
- [Proper and projective morphisms](proper-and-projective/README.md)

## Sheaves of modules

- [Modules and quasi-coherent sheaves](modules-and-quasicoherent/README.md)
- [Coherent sheaves and support](coherent-sheaves/README.md)
- [Projective sheaf machinery](projective-sheaves/README.md)
- [Later-used module exercises](module-exercises/README.md)

## Divisors and projective geometry

- [Weil and Cartier divisors, Picard groups, and K-theory](divisors/README.md)
- [Linear systems, ampleness, projective bundles, and blowups](projective-geometry/README.md)

## Differentials and regularity

- [Differentials, nonsingularity, canonical sheaves, and lci geometry](differentials/README.md)

## Sources

- [Hartshorne II.1 source notes](../../sources/hartshorne-ii-1.md)
- [Hartshorne II.2 source notes](../../sources/hartshorne-ii-2.md)
- [Hartshorne II.3 source notes](../../sources/hartshorne-ii-3.md)
- [Hartshorne II.4 source notes](../../sources/hartshorne-ii-4.md)
- [Hartshorne II.5 source notes](../../sources/hartshorne-ii-5.md)
- [Hartshorne II.6 source notes](../../sources/hartshorne-ii-6.md)
- [Hartshorne II.7 source notes](../../sources/hartshorne-ii-7.md)
- [Hartshorne II.8 source notes](../../sources/hartshorne-ii-8.md)
