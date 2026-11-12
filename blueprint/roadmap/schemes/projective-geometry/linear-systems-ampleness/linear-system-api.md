---
article_id: af_72a1a080625f60e38ac74daf
declaration: def
origin: cited
lean: Hartshorne.LinearSystem Hartshorne.globalSectionsOverField Hartshorne.LinearSystem.divisors Hartshorne.LinearSystem.divisor_eq_iff Hartshorne.LinearSystem.complete Hartshorne.LinearSystem.mem_divisors_complete_iff Hartshorne.LinearSystem.mem_divisors_complete_iff_weil Hartshorne.LinearSystem.divisors_mono Hartshorne.LinearSystem.le_complete Hartshorne.LinearSystem.dim Hartshorne.LinearSystem.IsBasePoint Hartshorne.LinearSystem.isBasePoint_iff Hartshorne.LinearSystem.mem_support_baseLocusIdeal_iff Hartshorne.LinearSystem.restrictionMap Hartshorne.LinearSystem.trace Hartshorne.IsDivisorIntersection Hartshorne.LinearSystem.mem_trace_divisors_iff Hartshorne.LinearSystem.pullbackGlobalSection_ne_zero_iff AlgebraicGeometry.Scheme.CartierDivisor.IsDivisorOfZeros.idealSheafData_eq_invertibleZeroIdeal Hartshorne.invertibleZeroIdeal Hartshorne.invertibleZeroIdeal_ideal_eq_span Hartshorne.mem_support_invertibleZeroIdeal_iff Hartshorne.invertibleZeroIdeal_map_iso Hartshorne.invertibleZeroIdeal_pullbackGlobalSection Hartshorne.baseLocusIdeal Hartshorne.baseLocus Hartshorne.mem_support_baseLocusIdeal_iff Hartshorne.linearSystemSection Hartshorne.linearSystem Hartshorne.linearSystemSection_single Hartshorne.mem_linearSystem Hartshorne.nonvanishingLocus_linearSystemSection_subset Hartshorne.linearSystemDomain Hartshorne.mem_linearSystemDomain_iff Hartshorne.range_baseLocus_subschemeι Hartshorne.span_germ_linearSystem_eq_top Hartshorne.linearSystemTwist Hartshorne.linearSystemSections Hartshorne.isGeneratedBySections_linearSystemSections
statement: formalized
proof: formalized
---

# Linear systems

A linear system is a finite-dimensional subspace of global
sections, considered modulo nonzero scalars, together with its
corresponding effective divisors. This describes complete systems,
linear subsystems, their projective dimensions, and base points.
Restriction along a closed immersion $i:Y\to X$ defines the trace
of a system on nonsingular projective varieties.

Geometrically, the trace contains $D\cdot Y$ only for divisors $D$ in the system
whose support does not contain $Y$; it is the system obtained from the images
of the sections under $\Gamma (X,L) \to \Gamma (Y,i^*L)$. No intersection divisor
is assigned when $Y$ lies in the support of $D$.

## Depends on

- [Divisors of invertible-sheaf sections](divisor-of-invertible-section.md)
- [Finite-dimensional projective global sections](../../projective-sheaves/projective-global-sections-finite.md)
- [Ambient hypersurfaces cut divisors](../../divisors/divisor-exercises/projective-intersection-divisor.md)
- [Morphisms from generated invertible sheaves](morphism-from-generated-line-bundle.md)
- [Finite-dimensional linear systems on an arbitrary variety](../../../cohomology/smooth-morphisms/finite-dimensional-linear-system-on-variety.md)

## Proof depends on

- Pullback of the associated invertible sheaf and restriction of sections
  along the closed immersion defining a trace.

## Sources

- [Hartshorne II.7, linear-system and trace definitions (pp.157–158)](../../../../sources/hartshorne-ii-7.md#morphisms-ampleness-and-linear-systems)
