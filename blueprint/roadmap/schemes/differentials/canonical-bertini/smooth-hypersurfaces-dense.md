---
article_id: af_4abc21f08a7265779b71f0f3
declaration: theorem
origin: cited
lean: Hartshorne.SmoothHypersurface.smooth_hypersurfaces_dense Hartshorne.SmoothHypersurface.hypersurfacePolynomial Hartshorne.SmoothHypersurface.dupleMonomial Hartshorne.SmoothHypersurface.hypersurfaceIdeal Hartshorne.SmoothHypersurface.hypersurfaceSection Hartshorne.SmoothHypersurface.hypersurfaceIdeal_ideal_basicOpen Hartshorne.SmoothHypersurface.mem_support_hypersurfaceIdeal_iff Hartshorne.SmoothHypersurface.isIntegral_hypersurface_of_isRegular
statement: formalized
proof: formalized
---

# Smooth hypersurfaces form a dense open family

Let $k$ be algebraically closed, $n \ge 2$, and $d \ge 1$. The degree-$d$
hypersurfaces in $\mathbb{P}^n_k$ that are nonsingular varieties form a dense open
subset of the complete linear system $|dH|$.

## Depends on

- [Linear systems](../../projective-geometry/linear-systems-ampleness/linear-system-api.md)
- [Regular points and nonsingular schemes](../scheme-differentials/regular-points-and-nonsingular-schemes.md)

## Proof depends on

- [The projective-space case of Bertini](bertini-projective-space-case.md)
- [Regular hyperplane sections](bertini-regular-hyperplane-section.md)
- [Projective intersections are nonempty](../../../intersections-projective-space/dimension/projective-intersection-nonempty.md)
- [Veronese Proj and twists](../../projective-sheaves/veronese-proj-twist.md), for the
  $d$-uple embedding, whose hyperplane sections are the degree-$d$ hypersurfaces.
- A regular hypersurface cannot have two irreducible components meeting at a
  point.
- The dimension theorem forces distinct positive-dimensional hypersurface
  components in $\mathbb{P}^n$, $n \ge 2$, to meet.

## Sources

- [Hartshorne II.8, Example 8.20.2 (p.183)](../../../../sources/hartshorne-ii-8.md#canonical-sheaves-and-adjunction)
