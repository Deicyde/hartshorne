# Degree of an ambient hypersurface section

## Supporting implementation references

- `deg(V.X) = deg(V) * deg(X)`

## Status: hypersurface case proved in Lean; divisor statement (faithfulness item 1) still to formalize

### Faithfulness item 1: divisors, not one hypersurface

Exercise II.6.2(c) states $\deg(D\cdot X) = (\deg D)(\deg X)$ for every divisor $D$ on
$\mathbb{P}^n$ none of whose components contains $X$. The article now states this, with $D\cdot X$
the linear extension that the dependency projective-intersection-divisor already defines and
formalizes (`Hartshorne.ambientDivisorsNotContaining`, `Hartshorne.projectiveIntersectionDivisorHom`),
and $\deg D$ the degree of a projective Weil divisor applied to $X = \mathbb{P}^n$ itself
(`Hartshorne.weilDivisorProjectiveDegree (𝟙 (Proj 𝒜))`). No new definition is needed in the DAG.
The Lean must add, besides the hypersurface declarations listed below, a theorem of the form
`weilDivisorProjectiveDegree ι (projectiveIntersectionDivisorHom ι hX D) =
weilDivisorProjectiveDegree (𝟙 (Proj 𝒜)) D * projectiveSpectrumPointDegree (ι.base (genericPoint X))`
for `D : ambientDivisorsNotContaining ι`, under `Nontrivial X`, proved by linearity from
`weilDivisorProjectiveDegree_projectiveIntersectionDivisor`, and record it in `lean:` too.

The scheme setting of the dependencies: $\mathbb{P}^n_k = \operatorname{Proj} S$ with
$S = k[x_0,\dots,x_n]$, $\iota : X \to \mathbb{P}^n_k$ a closed immersion with $X$ satisfying
$(*)$, $V$ a prime divisor of $\mathbb{P}^n_k$ with homogeneous equation $f$, $\mathfrak p$ the
homogeneous prime of $\iota(\eta_X)$, and $\mathfrak P_x$ that of $\iota(x)$. Degrees of points are
projective degrees of the classical zero sets $Z(\mathfrak P)$. Bézout (Theorem I.7.7) is applied
to the classical variety $Y = Z(\mathfrak p)$ and $H = Z(f)$.

### Statement needs $\dim X \ge 1$ (resolved by the roadmap revision)

For $X$ a closed point not on $V$, $V\cdot X = 0$ while $\deg V \cdot \deg X = \deg f \ge 1$.
The Bézout theorem the exercise invokes (I.7.7) assumes a variety of dimension at least one.
Resolved by the roadmap revision: the article now asserts the degree formula "when
$\dim X\ge 1$" and records the closed-point counterexample; the multiplicity equality (which
needs no bound) is unchanged. Formally the hypothesis is `Nontrivial X` (an integral scheme of
finite type over $k$ has more than one point exactly when its dimension is at least one); only
`weilDivisorProjectiveDegree_projectiveIntersectionDivisor` carries it, matching the article.
The ambient-divisor article (projective-intersection-divisor) needs no bound and is unchanged.

### To record (the statement is now corrected)

- `lean:` `Hartshorne.weilDivisorProjectiveDegree_projectiveIntersectionDivisor`
  `Hartshorne.projectiveIntersectionDivisor_apply_eq_projectiveIntersectionMultiplicity`
  `Hartshorne.closedImmersionComponentEquiv`
  `Hartshorne.projectiveIntersectionComponentPrime_closedImmersionComponentEquiv` (module
  `Hartshorne.Scheme.ProjectiveIntersectionDegreeFormula`), with `statement: formalized`,
  `proof: formalized`.
- The first theorem is $\deg(V\cdot X) = \deg V\deg X$; the second is "the valuation multiplicity
  along each component is the local intersection multiplicity", the components being matched by
  the equivalence.
- Edges the Lean uses (all statement and proof formalized) are now linked by the roadmap
  revision. Under Depends on, because the statements mention them:
  projective-intersection-multiplicity (the right side of the coefficient equality) and
  projective-intersection-components-minimal-primes (the component equivalence is built from
  `projectiveIntersectionComponentPrimeEquivMinimalPrimes`, and the fourth declaration's
  statement uses `projectiveIntersectionComponentPrime`). Under Proof depends on, used only in
  proofs: codimension-one-stalk-dvr, homogeneous-ideal-correspondence,
  projective-proper-closed-dimension-drop, projective-zero-dimensional-variety-point. The existing
  Depends on (projective-intersection-divisor, projective-weil-divisor-degree,
  projective-hypersurface-bezout) are all used. Projective-space-class-group is not used (and the
  article does not link it).

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
- Cleanup owed (duplicates): the copied helpers are gone. These modules now use the public
  `projectiveSpace_specializes_iff_le`, `exists_X_notMem_projectiveSpace` and
  `X_mem_irrelevant_projectiveSpace` (ProjectiveIntersectionDivisor) and
  `isProjAlgebraicSet_projZeroSet_of_isHomogeneous` (HilbertSerre). One item remains:
  - ProjectiveLocalIntersectionMultiplicity proves inline the fact
    `projectivePrimeDivisorEquation_notMem_of_not_subset` (ProjectiveIntersectionDegreeFormula);
    moving that lemma up into ProjectiveLocalIntersectionMultiplicity would remove the repeat.
  - `Hartshorne.EulerSequence.exists_X_notMem` (EulerSequenceChainRule) states the same fact as
    `exists_X_notMem_projectiveSpace` over the same grading; one of the two can go.
