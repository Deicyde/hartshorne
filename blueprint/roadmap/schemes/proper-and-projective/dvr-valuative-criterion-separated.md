---
article_id: af_76c399f9efcbb25ce4ccd596
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isSeparated_iff_dvr_valuativeCriterion
---

# DVR-valuative criterion for separatedness

Let $f : X \longrightarrow Y$ be a finite-type morphism of Noetherian schemes. Then $f$
is separated if and only if every valuative commutative square whose valuation
ring is a discrete valuation ring has at most one lift.

The forward implication restricts the ordinary uniqueness criterion. For the
converse, prove that the diagonal range is stable under specialization. An
equality specialization is immediate. For a strict specialization
$\Delta (x) \rightsquigarrow q$, the local domain of $q$ on the reduced closure of
$\Delta (x)$ has fraction field $\kappa (\Delta (x))$ and nonzero maximal ideal, and
it is Noetherian because $X \times_{Y} X$ is locally Noetherian: its projection
to the Noetherian scheme $X$ is a base change of $f$, hence locally of finite
type. Choose a dominating DVR of
$\kappa (\Delta (x))$, apply uniqueness to the two projected lifts, and conclude
that the specialized point remains on the diagonal. Quasi-compactness of the
diagonal, which holds because $X$ is Noetherian, then makes the range closed.

The Noetherian hypothesis on $Y$ is kept as in the source; it is not needed,
because the argument only uses that $X$ is Noetherian and that $f$ is locally of
finite type.

## Depends on

- [Valuative commutative squares](../separated-morphisms/valuative-square.md)
- [Separated morphisms](../separated-morphisms/separated-morphism.md)
- [Morphisms of finite type](../first-properties/finite-type.md)
- [Noetherian schemes and finite affine covers](../first-properties/noetherian-scheme.md)

## Proof depends on

- [A dominating DVR in a finitely generated extension](dominating-dvr-finitely-generated-extension.md)
- [Valuative criterion for separatedness](../separated-morphisms/valuative-criterion-separated.md)
- [Closed images and specialization](../separated-morphisms/quasi-compact-image-closed.md)
- [Maps from spectra of valuation rings](../separated-morphisms/valuation-spectrum-map-classification.md)

## Sources

- [Hartshorne II.4, separatedness clause of Exercise 4.11(b)](../../../sources/hartshorne-ii-4.md#adopted-exercises)
