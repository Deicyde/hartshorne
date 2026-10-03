---
declaration: theorem
origin: cited
source_units: [chapter-iv-section-4]
---

# Degree and kernel of general multiplication

Let `X` be an elliptic curve over an algebraically closed field of
characteristic different from two. For every nonzero integer `n`, the
multiplication morphism `[n]` is finite of degree `n^2`. If `n` is prime to
the characteristic, its closed kernel-point group is `(Z/nZ)^2`.

This is the point-kernel statement announced in Example 4.8.1. It does not
identify the possibly nonreduced finite kernel group scheme with a constant
group in characteristic dividing `n`.

## Depends on

- [Integer endomorphisms are injective and finite](../finite-multiplication/integer-endomorphisms-injective-finite.md)
- [Elliptic torsion count](../isogeny-exercises/elliptic-torsion-count.md)
- [Dual isogeny construction and functoriality](../isogeny-exercises/dual-isogeny-construction-functoriality.md)
- [Dual composites are multiplication](../isogeny-exercises/dual-composites-multiplication.md)
- [Dual additivity and self-duality of multiplication](../isogeny-exercises/dual-additivity-self-multiplication.md)
- [The dual preserves degree](../isogeny-exercises/dual-preserves-degree.md)

## Proof depends on

- Self-duality of `[n]` and the dual-composite formula give
  `deg([n])=n^2`.
- Prime-to-characteristic multiplication is étale. The hyperosculation
  theorem identifies its kernel points in characteristic zero; in positive
  characteristic, the standard finite-étale `n`-torsion theorem supplies the
  same point group independently of that proof.

## Sources

- [Hartshorne IV.4, Example 4.8.1 and its forward references, p.322](../../../../sources/hartshorne-iv-4.md)
- Silverman, *The Arithmetic of Elliptic Curves*, III.6.4, for prime-to-characteristic torsion.
