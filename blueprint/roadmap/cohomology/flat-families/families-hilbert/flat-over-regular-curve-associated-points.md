---
article_id: af_bda47588979c84d023027a74
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.flat_iff_forall_mem_associatedPoints_eq_genericPoint Hartshorne.forall_mem_associatedPoints_eq_genericPoint_iff_forall_dense_image Hartshorne.flat_iff_forall_mem_irreducibleComponents_dense_image
---

# Flatness over a regular curve

Let $f : X \to Y$, where $X$ is locally Noetherian and $Y$ is regular,
integral, and one-dimensional. Then $f$ is flat if and only if every
associated point of $X$ maps to the generic point of $Y$. If $X$ is reduced,
this is equivalent to every irreducible component of $X$ dominating $Y$.

The locally Noetherian source hypothesis makes explicit the hypothesis used
by Hartshorne's associated-prime argument. No weak-associated-point variant is
silently substituted.

Here regularity of $Y$ means that every local ring $\mathcal{O}_{Y,y}$ is a
regular local ring. Of the dimension hypothesis only $\dim Y \le 1$ is used: it
makes every local ring of $Y$ a field or a discrete valuation ring. The
equivalence between the associated-point condition and dominance of the
irreducible components holds for every reduced scheme $X$ and every integral
scheme $Y$, without the Noetherian, regularity, or dimension hypotheses.

## Depends on

- [Associated points of a scheme](scheme-associated-points.md)
- [The stalk criterion for flat morphisms](../flatness/flat-morphism-stalk-criterion.md)

## Proof depends on

- Every zero-divisor on a finite module over a Noetherian ring belongs to an
  associated prime.
- Associated points of a reduced locally Noetherian scheme are the generic
  points of its irreducible components.
- [Flat modules over a PID are torsion-free modules](../flatness/pid-flat-iff-torsion-free.md).
- [Codimension-one stalks are DVRs](../../../schemes/divisors/weil-divisors/codimension-one-stalk-dvr.md).

## Sources

- [Hartshorne III.9, Proposition 9.7, pp.257–258](../../../../sources/hartshorne-iii-9.md#dimensions-associated-points-and-flat-limits-pp256261)
