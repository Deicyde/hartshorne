---
article_id: af_f1dc2d1ecea71624686b695a
declaration: structure
origin: bridged
source_units: [chapter-v-section-6]
---

# Distinct interfaces for the four Kodaira-dimension-zero surface types

Over an algebraically closed field, keep the following structures distinct:

- a `K3Surface` is a Chapter-V surface with `K_X~0` and `q(X)=0`;
- an `EnriquesSurface` is a Chapter-V surface with `q(X)=0` and a nontrivial
  canonical class satisfying `2K_X~0`;
- an `AbelianSurface` is a projective connected group variety of dimension
  two;
- a `HyperellipticSurface` is the classical bielliptic quotient type
  `(E times F)/G`, with the finite group action free, translational on one
  elliptic factor, and with the other quotient equal to `P^1`.

The K3 and abelian-surface interfaces make sense in every characteristic.
For the Enriques and hyperelliptic interfaces used in Hartshorne's exhaustive
classification, impose `char k != 2,3`; the small-characteristic variants are
not silently included.

These are representation interfaces, not an assertion that every
Kodaira-dimension-zero surface has one of the structures.  In particular, a
hyperelliptic surface is not represented merely by the existence of some
elliptic fibration, and an abelian surface carries group data absent from the
other types.

## Depends on

- [Chapter-V surface convention](../../intersection-theory/foundations/surface-curve-convention.md)
- [The canonical divisor class](../../../schemes/differentials/canonical-bertini/canonical-divisor-class.md)
- [Elliptic group varieties](../../../curves/elliptic-curves/group-law-foundations/elliptic-group-variety.md)
- [The irregularity formula](../../../cohomology/serre-duality/duality-applications/smooth-surface-irregularity-formula.md)

## Sources

- [Hartshorne V.6, four surface types in Theorem 6.3, p.422](../../../../sources/hartshorne-v-6.md)
- Bombieri–Husemoller and Shafarevich for the classical quotient description.
