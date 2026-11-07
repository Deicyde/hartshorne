---
article_id: af_f1f2fa6af1f466bed9cd978d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.supportedSections Hartshorne.supportedSections_preservesFiniteLimits Hartshorne.mem_range_supportedSections_iff Hartshorne.cohomologyWithSupports Hartshorne.isRightAcyclic_supportedSections_of_isFlasque Hartshorne.openRestrict Hartshorne.cohomologyWithSupportsToCohomology Hartshorne.cohomologyRestriction Hartshorne.localizationδ Hartshorne.cohomologyWithSupportsToCohomology_mono Hartshorne.localization_exact₂ Hartshorne.localization_exact₃ Hartshorne.localization_exact₁
---

# The localization sequence for cohomology with supports

For a closed subset $Y \subseteq X$, the functor $\Gamma _Y(X,-)$ of global sections
supported in $Y$ is left exact. Define $H_Y^{n}(X,-)$ as its right derived
functors. If $U=X\setminus Y$, there is a natural localization long exact sequence

$0 \longrightarrow H_Y^{0}(X,F) \longrightarrow H^{0}(X,F) \longrightarrow H^{0}(U,F|_U) \longrightarrow H_Y^{1}(X,F) \longrightarrow \cdots$.

The unique main result is the localization sequence. Supporting clauses prove
that $\Gamma _Y(X,-)$ is left exact, identify the degree-zero kernel using the
subsheaf with support from II.1.20, and show that flasques are
$\Gamma _Y$-acyclic.

## Depends on

- [Right derived functors](../derived-functors/right-derived-functors.md)
- [Support of sections and sheaves](../../schemes/sheaf-functors/support-of-sections-and-sheaves.md)

## Proof depends on

- [Acyclic resolutions compute derived functors](../derived-functors/acyclic-resolution-comparison.md)
- [Flasque closure in short exact sequences](flasque-short-exact-closure.md)
- [Injective abelian sheaves are flasque](injective-abelian-sheaf-flasque.md)
- [Open extension by zero is left adjoint to restriction](../../schemes/sheaf-functors/open-extension-by-zero-adjunction.md)

## Informally uses

- [Restriction preserves stalks](../../schemes/sheaf-functors/restriction-stalk.md)
- [Injectives restrict to open subsets](../ext-groups/sheaf-ext/open-restriction-injective.md)

## Sources

- [Hartshorne III.2, Exercise 2.3 and adopted II.1.20, printed p. 212](../../../sources/hartshorne-iii-1-2.md#adopted-exercises-printed-pp-212213)

