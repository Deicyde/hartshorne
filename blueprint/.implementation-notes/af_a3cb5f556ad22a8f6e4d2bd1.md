# Degree of an ambient hypersurface section

## Supporting implementation references

- `deg(V.X) = deg(V) * deg(X)`

## Status: both missing ingredients built; the final assembly and a statement fix remain

The scheme setting of the dependencies: $\mathbb{P}^n_k = \operatorname{Proj} S$ with
$S = k[x_0,\dots,x_n]$, $\iota : X \to \mathbb{P}^n_k$ a closed immersion with $X$ satisfying
$(*)$, $V$ a prime divisor of $\mathbb{P}^n_k$ with homogeneous equation $f$ of degree $d$,
$\mathfrak p$ the homogeneous prime of $\iota(\eta_X)$, and $\mathfrak P_x$ that of $\iota(x)$.
Degrees of points are projective degrees of the classical zero sets $Z(\mathfrak P)$. Bézout
(Theorem I.7.7) is stated for the classical variety $Y = Z(\mathfrak p)$ and $H = Z(f)$.

### Statement needs $\dim X \ge 1$ (Roadmap return)

For $X$ a closed point not on $V$, $V\cdot X = 0$ while $\deg V \cdot \deg X = \deg f \ge 1$.
The article must add the hypothesis $\dim X \ge 1$ (as the Bézout article already does for its
variety). A convenient formal form is "$X$ has a point other than its generic point". The leaf
cannot be recorded until the statement carries this hypothesis.

### Checked declarations (sorry-free, axioms propext/Classical.choice/Quot.sound)

Module `Hartshorne.Scheme.ProjectiveIntersectionDegree` (earlier attempt):
- `projectivePrimeDivisorEquation_prime`, `projectivePrimeDivisorEquationDegree_pos`,
  `projectiveSpectrumPointDegree_primeDivisor` ($\deg V = \deg f$ for $n \ge 1$).

Module `Hartshorne.Scheme.ProjectiveClosedSubschemePrimes` (scheme-to-classical dictionary):
- `proj_specializes_iff_le`, `closedImmersion_specializes_iff`,
  `mem_range_closedImmersion_iff` (the image of $\iota$ is $\{q : \mathfrak p \subseteq q\}$).
- `not_lt_lt_of_mem_minimalPrimes_sup_span` (Krull's principal ideal theorem in $S/\mathfrak p$),
  `isHomogeneous_of_mem_minimalPrimes`.
- `coheight_eq_one_and_mem_iff_mem_minimalPrimes`: for homogeneous $f \notin \mathfrak p$,
  $x$ has codimension one and $f \in \mathfrak P_x$ iff $\mathfrak P_x$ is a minimal prime of
  $\mathfrak p + (f)$.
- `exists_closedImmersion_eq_of_mem_minimalPrimes`: every relevant minimal prime of
  $\mathfrak p + (f)$ is some $\mathfrak P_x$.

Module `Hartshorne.Scheme.ProjectiveLocalIntersectionMultiplicity` (local multiplicity):
- `homogeneousLocalizationIdeal`, `mk_mem_homogeneousLocalizationIdeal_iff`,
  `stalkMap_stalkIso_inv_eq_zero_iff` (stalk of $X$ at $x$ is
  $S_{(\mathfrak P_x)}/\mathfrak p_{(\mathfrak P_x)}$).
- `ringOrd_homogeneousLocalization_quotient_eq_length` (if $S_{(\mathfrak P)}/\mathfrak p_{(\mathfrak P)}$
  is a DVR, $\operatorname{ord}(f/g)$ there equals
  $\operatorname{length}_{S_{\mathfrak P}}(S/(\mathfrak p+(f)))_{\mathfrak P}$; proof via
  $S_{\mathfrak P}/\mathfrak p S_{\mathfrak P}$ being a DVR with the same uniformizer).
- `projectiveIntersectionDivisor_apply_eq_length`: for $x$ of codimension one, the coefficient of
  $V\cdot X$ at $x$ is a natural number $m$ with
  $\operatorname{length}_{S_{\mathfrak P_x}}(S/(\mathfrak p+(f)))_{\mathfrak P_x} = m$.
- Helpers: `quotient_mk_mem_maximalIdeal`, `length_localizedModule_quotient`,
  `exists_X_notMem_asHomogeneousIdeal`, `ord_algebraMap_stalk_eq_of_ringOrd`,
  instance `isPrime_asHomogeneousIdeal_base`.

The class group of $\mathbb{P}^n$ is not needed.

### Remaining goal

With $\dim X \ge 1$ added:
`weilDivisorProjectiveDegree ι (projectiveIntersectionDivisor ι hX V) =
projectiveSpectrumPointDegree V.1 * projectiveSpectrumPointDegree (ι.base (genericPoint X))`.

### Next route (assembly only)

1. Classical side: $Y = Z(\mathfrak p)$ is a projective variety and $J(Y) = \mathfrak p$, and
   $J(Z(f)) = (f)$ (`homogeneousVanishingIdeal_projZeroSet` with `projZeroSet_span`; the zero sets
   are nonempty by `projZeroSet_eq_empty_iff` and relevance). So
   `projectiveIntersectionIdeal Y H` $= \mathfrak p + (f)$, and $Y \not\subseteq H$ as
   $f \notin \mathfrak p$.
2. `projectiveIntersectionComponentPrimeEquivMinimalPrimes` identifies the components with the
   homogeneous minimal primes $Q$ of $\mathfrak p + (f)$ with $Z(Q) \ne \varnothing$, i.e. relevant
   $Q$ (`projZeroSet_eq_empty_iff`; bridge the project's `irrelevantIdeal` with
   `HomogeneousIdeal.irrelevant`). The two dictionary theorems above turn these into the prime
   divisors $x$ of $X$ with $f \in \mathfrak P_x$; the other prime divisors have coefficient zero
   (`projectiveIntersectionDivisor_apply_eq_zero_of_notMem`).
3. Reindex the `finsum` in `weilDivisorProjectiveDegree_apply` as the Bézout `Finset` sum. Match
   coefficients with `projectiveIntersectionDivisor_apply_eq_length` and
   `natCast_projectiveIntersectionMultiplicity`, and degrees with
   `projectiveSpectrumPointDegree_cast` and `projectiveIntersectionComponentPrime_projZeroSet`.
4. Apply `projective_hypersurface_bezout` with $r$ from `exists_projDim_eq_nat_of_isProjVariety`.
   $r > 0$ comes from the dimension hypothesis via
   `IsProjVariety.eq_singleton_of_projDim_eq_zero`: a point $x \ne \eta$ would give the
   irreducible closed $Z(\mathfrak P_x) \subsetneq Y$. Then rewrite $\deg H$ as
   `projectiveSpectrumPointDegree V.1` via `span_projectivePrimeDivisorEquation` and
   `projZeroSet_span`.
