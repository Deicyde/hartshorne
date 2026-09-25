---
article_id: af_ce39f8914d2433976bdb3455
declaration: theorem
origin: cited
source_units: [chapter-i-section-4, chapter-i-section-6-abstract-curves]
statement: formalized
proof: formalized
lean: Hartshorne.IsQuasiProjVariety.isCurve_infinite_and_isClosed_iff
---

# Quasi-projective curves have the cofinite topology

Let `Y` be a quasi-projective curve over the algebraically closed field `k`.
Then `Y` has infinitely many points, and every proper closed subset of `Y` is
finite.  Equivalently, its Zariski topology is the cofinite topology.

Projective linear forms separate points, so the Zariski topology is T₁.  A
finite T₁ space is discrete and has topological Krull dimension at most zero,
which proves infinitude.  For the closed-set statement, decompose a proper
closed subset into finitely many irreducible closed components.  In an
irreducible space of dimension one, each proper irreducible closed subset is
minimal; the closed singleton below it therefore shows that it is a point.
Do not formalize Exercise 4.8(a)'s stronger cardinality equality or part (b),
since Proposition 6.7 needs neither.

This result is separated from the construction of `C_K`: it also proves that
the point-to-local-ring map between a curve and its image is a homeomorphism
once that image is known to be open.

## Depends on

- [Curves](../nonsingular-curves/curve.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)

## Proof depends on

- [Decomposition into irreducible components](../affine-varieties/irreducible-decomposition.md)
- [Linear fractions separate projective points](../nonsingular-curves/projective-linear-separation.md)

## Sources

- [Hartshorne I.4, Exercise 4.8(a), and I.6 before Proposition 6.7 (pp. 31, 42)](../../sources/hartshorne.md#i4)
- [Hartshorne I.6, cofinite topology on `C_K` (p. 42)](../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
