---
article_id: af_c25452c2234849d3af094f90
declaration: theorem
origin: cited
source_units: [appendix-c-section-1]
---

# The projective line has `q^r+1` points over `F_(q^r)`

For every `r>=1`,

`N_r(P^1/F_q)=q^r+1`.

## Depends on

- [The finite-extension point-count sequence](point-count-sequence.md)
- [Scheme-valued points of the projective line](projective-line-scheme-points.md)
- [Projective space is proper](../../schemes/proper-and-projective/projective-space-proper.md)

## Proof depends on

- The standard affine chart contributes `q^r` points and the hyperplane at
  infinity contributes one point.
- `Projectivization.card_of_finrank_two` counts the corresponding classical
  projective lines over the finite extension field.
- `Hartshorne.finiteFieldExtension_natCard` identifies that field's cardinality
  with `q^r`.

## Sources

- [Hartshorne Appendix C.1, projective-line example, p.450](../../../sources/hartshorne-appendix-c-1.md)
