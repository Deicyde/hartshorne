# Degree of an ambient hypersurface section

## Supporting implementation references

- `deg(V.X) = deg(V) * deg(X)`

## Status: proved in Lean with the extra hypothesis dim X ≥ 1; unrecorded pending a statement fix

The scheme setting of the dependencies: $\mathbb{P}^n_k = \operatorname{Proj} S$ with
$S = k[x_0,\dots,x_n]$, $\iota : X \to \mathbb{P}^n_k$ a closed immersion with $X$ satisfying
$(*)$, $V$ a prime divisor of $\mathbb{P}^n_k$ with homogeneous equation $f$, $\mathfrak p$ the
homogeneous prime of $\iota(\eta_X)$, and $\mathfrak P_x$ that of $\iota(x)$. Degrees of points are
projective degrees of the classical zero sets $Z(\mathfrak P)$. Bézout (Theorem I.7.7) is applied
to the classical variety $Y = Z(\mathfrak p)$ and $H = Z(f)$.

### Statement needs $\dim X \ge 1$ (Roadmap return)

For $X$ a closed point not on $V$, $V\cdot X = 0$ while $\deg V \cdot \deg X = \deg f \ge 1$.
The blueprint's source page paraphrases the preamble as "a projective variety nonsingular in
codimension one" and states no dimension bound; the Bézout theorem it invokes (I.7.7) assumes a
variety of dimension at least one. Proposed wording for the article: "Let $X$ have dimension at
least one" added to the setting, i.e. "In the setting of the ambient intersection divisor, assume
moreover $\dim X \ge 1$." Formally the hypothesis is `Nontrivial X` (an integral scheme of finite
type over $k$ has more than one point exactly when its dimension is at least one).

### To record once the statement is corrected

- `lean:` `Hartshorne.weilDivisorProjectiveDegree_projectiveIntersectionDivisor`
  `Hartshorne.projectiveIntersectionDivisor_apply_eq_projectiveIntersectionMultiplicity`
  `Hartshorne.closedImmersionComponentEquiv`
  `Hartshorne.projectiveIntersectionComponentPrime_closedImmersionComponentEquiv` (module
  `Hartshorne.Scheme.ProjectiveIntersectionDegreeFormula`), with `statement: formalized`,
  `proof: formalized`.
- The first theorem is $\deg(V\cdot X) = \deg V\deg X$; the second is "the valuation multiplicity
  along each component is the local intersection multiplicity", the components being matched by
  the equivalence.
- Link-only Depends-on edges the Lean then uses (all recorded on main, statement and proof
  formalized): projective-intersection-multiplicity, projective-intersection-components-minimal-primes,
  homogeneous-ideal-correspondence, projective-proper-closed-dimension-drop,
  projective-zero-dimensional-variety-point, codimension-one-stalk-dvr. The existing Depends on
  (projective-intersection-divisor, projective-weil-divisor-degree, projective-hypersurface-bezout)
  are all used. Projective-space-class-group is not used.

### Lean layout

- `Hartshorne.Scheme.ProjectiveIntersectionDegree`: $f$ prime, $\deg f > 0$, $\deg V = \deg f$.
- `Hartshorne.Scheme.ProjectiveClosedSubschemePrimes`: codimension-one points of $X$ on $f = 0$ are
  the relevant minimal primes of $\mathfrak p + (f)$ (Krull in $S/\mathfrak p$).
- `Hartshorne.Scheme.ProjectiveLocalIntersectionMultiplicity`: the stalk is
  $S_{(\mathfrak P)}/\mathfrak p_{(\mathfrak P)}$ and $\operatorname{ord}_x(f/g)$ is the length of
  $(S/(\mathfrak p+(f)))_{\mathfrak P}$ (`projectiveIntersectionDivisor_apply_eq_length`).
- `Hartshorne.Scheme.ProjectiveIntersectionDegreeFormula`: classical identifications
  ($J(Z(\mathfrak p)) = \mathfrak p$, $J(Z(f)) = (f)$, relevance iff nonempty zero set), the
  component equivalence, and the Bézout assembly.
- Cleanup owed (duplicates):
  - `exists_X_notMem_asHomogeneousIdeal` copies the private `exists_projectiveSpace_X_notMem`
    (ProjectiveIntersectionDivisor); the public `Hartshorne.EulerSequence.exists_X_notMem` exists.
  - `isProjAlgebraicSet_projZeroSet_of_isHomogeneousIdeal` copies the private
    `isProjAlgebraicSet_projZeroSet_of_isHomogeneous` (HilbertSerre, TopDimensionalPrimeFiltrationLeadingTerm).
  - `proj_specializes_iff_le` duplicates the public `projectiveSpace_specializes_iff_le`
    (ProjectiveSpaceClassGroup).
  - The irrelevant-ideal step in ProjectiveIntersectionDegreeFormula reproves
    `X_mem_irrelevant_projectiveSpace` (ProjectiveSpaceClassGroup).
  - ProjectiveLocalIntersectionMultiplicity proves inline the fact
    `projectivePrimeDivisorEquation_notMem_of_not_subset` (ProjectiveIntersectionDegreeFormula).
