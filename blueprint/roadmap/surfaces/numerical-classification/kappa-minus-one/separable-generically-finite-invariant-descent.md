---
declaration: theorem
origin: cited
source_units: [chapter-v-section-6]
not_ready: true
---

# Separable generically finite maps descend surface invariants

Let `F:X dashedrightarrow Y` be a dominant generically finite separable
rational map between nonsingular projective surfaces over an algebraically
closed field.  Then

`p_g(Y)<=p_g(X)`, `P_2(Y)<=P_2(X)`, and `q(Y)<=q(X)`.

The first two inequalities come from injective pullback of canonical and
bicanonical forms on the common regular domain.  The irregularity inequality
uses the separable pullback on the Picard/Albanese tangent space.  It is not a
trace-splitting argument requiring the degree to be invertible in the ground
field.

This node is not ready: the characteristic-aware Picard/Albanese theorem
giving finite kernel and injective tangent pullback has no adopted exact
source or project API.

## Depends on

- [Geometric genus](../../../schemes/differentials/canonical-bertini/geometric-genus.md)
- [Birational invariance of plurigenera](../../../schemes/differentials/differential-exercises/plurigenus-birational-invariant.md)
- [The irregularity formula](../../../cohomology/serre-duality/duality-applications/smooth-surface-irregularity-formula.md)
- [The maximal domain of a birational transformation](../../birational-transformations/fundamental-loci/birational-transformation-maximal-domain.md)

## Proof depends on

- Separability makes the generic pullback of top differential forms
  injective; extension across codimension two produces global pullbacks.
- The Picard/Albanese pullback for a generically finite separable map has
  finite kernel and injective tangent map, yielding the inequality for `q`.

## Sources

- [Hartshorne V.6, proof outline in Remark 6.2.1, p.422](../../../../sources/hartshorne-v-6.md)
- Serre [13] and Zariski [9].
