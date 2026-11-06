---
article_id: af_e067734e3eaa60839252f909
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.SchemeRationalMap.normal_projective_fundamentalLocus_codim_two Hartshorne.SchemeRationalMap.normal_projective_surface_fundamentalLocus_finite Hartshorne.SchemeRationalMap.mem_dom_of_coheight_eq_one Hartshorne.SchemeRationalMap.two_le_codim_fundamentalLocus Hartshorne.SchemeRationalMap.fundamentalLocus_finite_of_topologicalKrullDim_eq_two
---

# The fundamental locus on a normal source has codimension at least two

Let $T:X \dashrightarrow Y$ be a birational transformation of projective
varieties, with $X$ normal. Its fundamental locus is closed and has
codimension at least two. In particular, for a normal surface it is a finite
set of closed points.

The integrality of $Y$ is kept as in the source; it is not needed, because
the argument uses only that $Y$ is projective, hence proper, over the field.

## Depends on

- [The maximal domain of a birational transformation](birational-transformation-maximal-domain.md)
- [Valuative criterion for properness](../../../schemes/proper-and-projective/valuative-criterion-proper.md)
- [Codimension-one stalks are DVRs](../../../schemes/divisors/weil-divisors/codimension-one-stalk-dvr.md)
- [Normal schemes](../../../schemes/normalization-and-exercises/normal-scheme.md)

## Proof depends on

- Properness extends the generic morphism over every codimension-one DVR;
  the local extension is represented on an open neighborhood.

## Sources

- [Hartshorne V.5, Lemma 5.1, p.410](../../../../sources/hartshorne-v-5.md)
