# The localization sequence for cohomology with supports

## Partial progress

The module `Hartshorne.Cohomology.CohomologyWithSupports` is sorry-free and not
recorded in the article frontmatter. For a closed subset $Y$ of a topological
space $X$, with $U = X \setminus Y$, it proves:

- `Hartshorne.supportedSections`: the functor $\Gamma_Y(X,-)$ on abelian
  sheaves, defined as the kernel of restriction $\Gamma(X,-)\to\Gamma(U,-)$.
  It is left exact and additive
  (`Hartshorne.supportedSections_preservesFiniteLimits`,
  `Hartshorne.supportedSections_additive`).
- `Hartshorne.mem_range_supportedSections_iff`: the elements of
  $\Gamma_Y(X,F)$ are exactly the global sections whose support (in the sense
  of II.1.20) lies in $Y$. This is proved through
  `Hartshorne.restrict_closedComplement_eq_zero_iff`.
- `Hartshorne.cohomologyWithSupports`: $H^n_Y(X,-)$, the right derived
  functors of $\Gamma_Y(X,-)$, together with
  `Hartshorne.cohomologyWithSupportsZeroIso`, $H^0_Y \cong \Gamma_Y$.
- `Hartshorne.supportedSectionsSC_shortExact_of_isFlasque`: for flasque $F$,
  $0\to\Gamma_Y(X,F)\to\Gamma(X,F)\to\Gamma(U,F)\to0$ is exact (Exercise 2.3(c)).
- `Hartshorne.supportedSections_map_epi_of_shortExact`: if
  $0\to F'\to F\to F''\to0$ is exact and $F'$ is flasque, then
  $\Gamma_Y(X,F)\to\Gamma_Y(X,F'')$ is surjective.
- `Hartshorne.isRightAcyclic_of_shortExact_injective`: general dimension
  shifting. Let $P$ be a property of objects. Suppose that for every short
  exact sequence $0\to A\to I\to G\to 0$ with $P(A)$ and $I$ injective, $P(G)$
  holds and $F(I)\to F(G)$ is surjective. Then every object with property $P$
  is $F$-acyclic.

## Blockers

1. **Dependency edges missing.** For flasques to be $\Gamma_Y$-acyclic
   (Exercise 2.3(d)), the lemma above must be applied to the class of flasque
   sheaves. That step needs injective abelian sheaves to be flasque, which is
   owned by `cohomology/sheaf-cohomology/injective-abelian-sheaf-flasque`
   (formalized). This article's dependency lists do not reach it, even
   transitively.
2. **Unformalized prerequisite.** The term $H^n(U,F|_U)$ is computed from
   $\Gamma(U,I|_U)$ for an injective resolution $I$ of $F$. That requires the
   flasque sheaves $I^k|_U$ to be $\Gamma(U,-)$-acyclic, which is
   `cohomology/sheaf-cohomology/flasque-sheaf-acyclic` (III.2.5). That article
   is planned and not reached by this article. It depends on
   `cohomology/sheaf-cohomology/sheaf-cohomology`, which is `not_ready`. The
   alternative, that restricting an injective abelian sheaf to an open subset
   gives an injective sheaf, exists in the roadmap only for module sheaves
   (`cohomology/ext-groups/sheaf-ext/open-restriction-injective`).
   Once injectives are known to be flasque, III.2.5 follows from the lemma
   above together with Mathlib's
   `TopCat.Sheaf.IsFlasque.epi_of_shortExact` and
   `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂`.
3. **Sheaf cohomology.** The statement uses $H^n(X,F)$ and $H^n(U,F|_U)$.
   The project's sheaf-cohomology article has no Lean declaration yet. Defining
   it here as the right derived functors of global sections would conflict
   with that article.

## Next route

Once the edges are in place:

1. Apply the dimension-shifting lemma to get flasque acyclicity for
   $\Gamma_Y(X,-)$, $\Gamma(X,-)$ and $\Gamma(U,-)$.
2. For the chosen injective resolution $I$ of $F$, form the degreewise short
   exact sequence of complexes
   $0\to\Gamma_Y(X,I)\to\Gamma(X,I)\to\Gamma(U,I|_U)\to0$ and take its homology
   sequence (Mathlib's `HomologicalComplex.HomologySequence`).
3. Identify the third complex with $\Gamma(U,-)$ applied to the restricted
   resolution, using `TopCat.Sheaf.pullback` along the open inclusion.
   Restriction is exact because it preserves stalks (restriction-stalk), so
   $I|_U$ is a flasque resolution of $F|_U$. Then apply
   `Hartshorne.acyclicResolutionIso`.
4. Naturality in $F$ follows from `InjectiveResolution.desc`, the naturality
   of the homology-sequence connecting maps, and
   `Hartshorne.acyclicResolutionIso_naturality`.
