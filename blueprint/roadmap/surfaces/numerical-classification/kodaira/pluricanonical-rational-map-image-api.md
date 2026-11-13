---
article_id: af_3122495be6d2ec287ac6e2a2
declaration: def
origin: bridged
lean: Hartshorne.pluricanonicalMap Hartshorne.pluricanonicalSystem Hartshorne.mem_pluricanonicalDomain_iff Hartshorne.pluricanonicalImage Hartshorne.pluricanonicalImageDim Hartshorne.pluricanonicalSystem_divisors_eq_empty_iff Hartshorne.pluricanonicalSystem_dim_eq_neg_one_iff Hartshorne.pluricanonicalImageDim_eq_zero Hartshorne.pluricanonicalMap_eq_of_fixedPart Hartshorne.pluricanonicalImage_eq_of_fixedPart Hartshorne.linearSystemMorphism_map
statement: formalized
proof: formalized
---

# Pluricanonical rational maps and their image dimensions

For $n>0$ with $H^0(X,\omega _X^n)$ nonzero, define the pluricanonical rational
map

$\phi _n : X \dashrightarrow P(H^0(X,\omega _X^n))$

in the project's quotient-projective-space convention, on the complement of
the base locus of $|nK|$. Define its image as the
closure of the image of that domain, and record its dimension. Removing a
fixed divisorial part does not change the rational map or image.

If the section space is zero, record that $|nK|$ is empty and do not invent a
map to an empty projective space. If it is one-dimensional, the image has
dimension zero.

## Depends on

- [The canonical section ring](canonical-section-ring.md)
- [Linear systems](../../../schemes/projective-geometry/linear-systems-ampleness/linear-system-api.md)
- [Rational maps](../../../rational-maps/rational-map.md)
- [Projective closure](../../../rational-maps/projective-closure.md)
- [Finite-dimensional linear systems on an arbitrary variety](../../../cohomology/smooth-morphisms/finite-dimensional-linear-system-on-variety.md)

## Proof depends on

- [The universal property of a blowup](../../../schemes/projective-geometry/blowups/universal-property.md)

## Sources

- [Hartshorne V.6, pluricanonical-map formulation, pp.421–422](../../../../sources/hartshorne-v-6.md)
