---
article_id: af_d36c8574cc6f669d4441c1d4
declaration: theorem
origin: cited
lean: Hartshorne.BertiniIncidence.bertini_avoid_finite_singular_set Hartshorne.BertiniIncidence.hyperplanes_avoiding_finite_set_dense Hartshorne.BertiniIncidence.bertini_regular_hyperplane_section_avoiding
statement: formalized
proof: formalized
---

# Bertini with finitely many singular points

Let $X$ be a closed subvariety of $\mathbb{P}^n_k$, with $k$ algebraically closed,
having only finitely many singular points. The hyperplanes $H$ that contain none
of these points and do not contain $X$, and for which the scheme $H \cap X$ is
regular at every point, form an open dense subset of the complete linear system
$|H|$.

The reason (p.180): for a finite set $S$ of closed points of $\mathbb{P}^n_k$, the
hyperplanes containing no point of $S$ form an open dense subset of $|H|$.

For nonsingular $X$ one may also require $H$ to avoid a given finite set of
closed points; Hartshorne does not state this.

## Depends on

- [Regular hyperplane sections](bertini-regular-hyperplane-section.md)

## Proof depends on

- Hyperplanes through a fixed projective point form a proper closed linear
  subsystem.
- A finite union of proper closed subsets of an irreducible projective space
  is proper.

## Sources

- [Hartshorne II.8, Remark 8.18.1 (p.180)](../../../../sources/hartshorne-ii-8.md#nonsingular-varieties-and-bertini)
