# Hartshorne Appendix B, sections 3–4

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Appendix B, §§3–4, printed pp.441–446.  Section 3 begins after the projective
GAGA and Chow discussion on p.441.  Section 4 ends on p.446 immediately
before the exponential sequence.

All substantive statements are over `C`.  Algebraic schemes are finite type
over `C`; analytic spaces are Grauert complex analytic spaces.  The source
mixes schemes, analytic spaces, complex manifolds, topological covering
spaces, differential forms, and singular cohomology.  Those categories and
their comparison functors must remain distinct.

## Algebraization and Riemann existence, printed pp.441–442

A compact complex manifold has at most one algebraization: if a finite-type
`C`-scheme `X` with `X^h` isomorphic to the manifold exists, compactness makes
`X` proper and proper GAGA/full faithfulness gives uniqueness.

Theorem 3.1 says every compact complex one-manifold is projective algebraic.
Hartshorne outlines two inputs:

1. hard analysis produces a nonconstant global meromorphic function, via
   Weyl's Dirichlet-principle method or Gunning's distribution/cohomology
   method;
2. the function gives a finite holomorphic map to `P^1`, which Riemann
   existence algebraizes as a smooth projective curve.

Theorem 3.2, generalized Riemann existence, states: let `X` be a normal
finite-type `C`-scheme, and let `f:X'_an->X^h` be a finite morphism from a
normal complex analytic space.  Here analytic finite means proper with finite
fibres.  There is a unique normal finite-type scheme `X'`, finite over `X`,
whose analytification, including its morphism, is `f`.  Hartshorne cites
Grauert–Remmert and SGA 1, Exposé XII.

For connected normal `X` and a basepoint, finite étale algebraic covers are
therefore equivalent to finite unramified topological covers of `X^h`.  The
algebraic fundamental group is the profinite completion of the usual
topological fundamental group.

## Meromorphic functions and Moishezon manifolds, printed pp.442–445

For a connected compact complex manifold `M`, let `K(M)` be its field of
global meromorphic functions.  Siegel's Proposition 3.3 says

`trdeg_C K(M) <= dim_C M`.

Hartshorne explicitly asserts finite generation at least in the equality
case; no stronger finite-generation statement is adopted.

If `M=X^h` is algebraic and compact, analytic meromorphic functions agree
with the rational function field `K(X)`, so equality holds.  A compact
complex `n`-manifold with equality is called a Moishezon manifold.

For `n>=2`, a sufficiently general complex torus `C^n/Lambda` has no
nonconstant meromorphic functions.  Chow–Kodaira Theorem 3.4 says a compact
complex surface with two algebraically independent meromorphic functions is
projective algebraic.  In dimension at least three, Hironaka and Moishezon
construct nonalgebraic Moishezon manifolds, while Moishezon proves that every
Moishezon manifold becomes projective algebraic after finitely many analytic
monoidal transformations with nonsingular centres.

Examples 3.4.1–3.4.2 describe Hironaka's detailed constructions of a smooth
complete nonprojective algebraic threefold and a nonalgebraic Moishezon
threefold.  Remark 3.4.3 quotes Artin's equivalence between smooth proper
algebraic spaces over `C` and Moishezon manifolds.  These constructions and
the algebraic-space theorem are retained as contextual counterexamples, not
as fine-roadmap leaves in the present scope.

## Kähler and Hodge manifolds, printed pp.445–446

A Hermitian metric on a complex manifold is Kähler when its associated real
two-form of type `(1,1)` is closed.  A Kähler manifold is a complex manifold
equipped with such a metric.  Projective space has the Fubini–Study Kähler
metric, and smooth projective algebraic varieties inherit Kähler metrics.

A compact Kähler manifold is a Hodge manifold when it admits a Kähler form
whose class in `H^2(M,C)` lies in the image of `H^2(M,Z)`.  The normalization
of this integrality statement must be fixed consistently with the chosen
de Rham/singular comparison.

Kodaira's Theorem 4.1 says every Hodge manifold is projective algebraic.  The
Fubini–Study class supplies the converse, so for compact complex manifolds

`Hodge <-> projective algebraic`.

Every compact complex curve is Hodge.  Moishezon's Theorem 4.2 says every
compact Kähler Moishezon manifold is projective algebraic.  Hartshorne's
summary diagram also distinguishes abstract algebraicity from projectivity;
the general tori and Hironaka examples show that no additional implications
can be added.

The introductory references to Hodge decomposition, Kodaira–Nakano and
Grauert–Riemenschneider vanishing, intermediate Jacobians, and period maps
are historical context rather than §4 theorem targets.

## Exercise disposition, printed pp.447–448

- Exercises B.6.1–B.6.4 concern the basic/nonproper analytification failures
  of §§1–2 and are outside this source unit.
- Exercise B.6.5, analytic rigidity of smooth affine algebraic curves, is a
  useful optional consequence of curve compactification and Riemann
  existence, but has no later running dependency and is not adopted here.
- Exercise B.6.6, algebraization and uniqueness of analytic morphisms between
  projective schemes, is adopted in the §§1–2 roadmap and is reused for the
  uniqueness statement at the start of §3.
- No exercise directly proves the Kähler or Moishezon theorems.

## Proof sources and blockers

Exact proof-level sources are required from:

- Weyl or Gunning for meromorphic functions on compact Riemann surfaces;
- Grauert–Remmert and SGA 1 XII for generalized Riemann existence;
- Siegel for the meromorphic-function-field bound;
- Morrow–Kodaira for generic tori of algebraic dimension zero;
- Chow–Kodaira and Moishezon for surface algebraicity and projective
  modification;
- Kodaira for the Hodge embedding theorem;
- Moishezon for the Kähler–Moishezon projectivity theorem.

The present project has no differential-geometric complex-manifold/Kähler
API, analytic meromorphic-function fields, analytic finite morphisms, or
analytic modification theory.  The corresponding theorem leaves are source
or representation blockers.  Hironaka's detailed gluing and Artin's
algebraic-space comparison would require separate milestones.

## Pinned Mathlib audit and false friends

The pinned checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`).  No §3–4 leaf is
an exact Mathlib result.

Mathlib has covering-space and fundamental-groupoid infrastructure and
one-variable meromorphic-function theory, but no Grauert analytic spaces,
scheme analytification, Riemann existence, compact complex-manifold,
Moishezon, or Kodaira embedding theory.  `RingTheory.Kaehler` concerns
algebraic Kähler differentials and is unrelated to Kähler metrics.  The
two-dimensional inner-product-space Kähler form is not a manifold-level
Kähler geometry API.

## Representation warnings

- “Algebraic” means isomorphic to the analytification of a finite-type
  `C`-scheme; “projective algebraic” is stronger.
- Preserve nonreduced analytic spaces in generalized Riemann existence.
- Analytic finite means proper with finite fibres before it is compared with
  algebraic finiteness.
- Fundamental groups and covering categories require connectedness and
  basepoints; the completion is profinite.
- A general complex torus is not an abelian variety.
- Analytic monoidal transformations and analytic gluing are not scheme
  blowups by definitional equality.
- Kähler forms are closed positive real `(1,1)`-forms, not algebraic Kähler
  differentials.
- A Hodge manifold admits an integral Kähler class; do not require every
  Kähler metric to have integral class.
- Fix the comparison and normalization relating differential-form classes,
  singular cohomology, and integral cohomology.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Uniqueness of compact algebraization | `transcendental-methods/algebraicity/compact-analytic-algebraization-uniqueness.md` |
| Meromorphic function on a compact curve | `transcendental-methods/algebraicity/compact-riemann-surface-meromorphic-function.md` |
| Analytic finite-morphism interface | `transcendental-methods/algebraicity/analytic-finite-morphism-api.md` |
| Theorem 3.1 | `transcendental-methods/algebraicity/riemann-compact-curve-projective.md` |
| Theorem 3.2 | `transcendental-methods/algebraicity/generalized-riemann-existence.md` |
| Finite-cover equivalence | `transcendental-methods/algebraicity/finite-etale-analytic-cover-equivalence.md` |
| Fundamental-group comparison | `transcendental-methods/algebraicity/algebraic-fundamental-group-profinite-completion.md` |
| Meromorphic-function field | `transcendental-methods/algebraicity/compact-meromorphic-function-field.md` |
| Siegel bound | `transcendental-methods/algebraicity/siegel-meromorphic-trdeg-bound.md` |
| Algebraic meromorphic/rational comparison | `transcendental-methods/algebraicity/algebraic-meromorphic-rational-field.md` |
| Moishezon definition | `transcendental-methods/algebraicity/moishezon-manifold.md` |
| General torus example | `transcendental-methods/algebraicity/general-torus-algebraic-dimension-zero.md` |
| Theorem 3.4 | `transcendental-methods/algebraicity/moishezon-surface-projective.md` |
| Moishezon projective modification | `transcendental-methods/algebraicity/moishezon-projective-modification.md` |
| Hermitian/Kähler interface | `transcendental-methods/kahler/hermitian-kahler-manifold-api.md` |
| Hodge-manifold interface | `transcendental-methods/kahler/hodge-manifold-integral-kahler-class.md` |
| Projective manifolds are Hodge | `transcendental-methods/kahler/projective-fubini-study-hodge.md` |
| Theorem 4.1 | `transcendental-methods/kahler/kodaira-hodge-embedding.md` |
| Compact curves are Hodge | `transcendental-methods/kahler/compact-complex-curves-hodge.md` |
| Theorem 4.2 | `transcendental-methods/kahler/kahler-moishezon-projective.md` |
| Implication diagram | `transcendental-methods/kahler/compact-manifold-algebraicity-implication-diagram.md` |

## Reused prerequisite map

| Source result | Existing roadmap article |
|---|---|
| Complex analytic spaces | `transcendental-methods/analytic-spaces/complex-analytic-space.md` |
| Analytification functor | `transcendental-methods/analytification/analytification-functor.md` |
| Proper iff compact | `transcendental-methods/comparison/proper-scheme-iff-compact.md` |
| Smooth iff complex manifold | `transcendental-methods/comparison/smooth-iff-complex-manifold.md` |
| Projective GAGA coherent equivalence | `transcendental-methods/gaga/projective-gaga-coherent-equivalence.md` |
| Proper GAGA extension | `transcendental-methods/gaga/proper-gaga-extension.md` |
| Chow algebraization | `transcendental-methods/gaga/chow-analytic-subspace-algebraization.md` |
| Exercise B.6.6 | `transcendental-methods/gaga/exercises/projective-analytic-morphism-algebraization.md` |
