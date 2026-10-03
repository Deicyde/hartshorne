# Hartshorne III.11–12, formal functions and semicontinuity

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter III, §§11–12, printed pp.276–292. Section 11 occupies pp.276–281;
§12 begins on p.281 and its exercises end on p.292. This roadmap adopts all
named results in the running text and only the exercises with an identified
later dependency.

These sections share a strict hypothesis boundary. Formal functions is stated
for a projective morphism of Noetherian schemes and a coherent sheaf. The
semicontinuity section fixes a projective morphism `f : X -> Spec A`, with `A`
Noetherian, and a coherent `O_X`-module `F` flat over `A`; its global theorems
are then obtained by localization on a Noetherian target. No result below is
silently strengthened from projective to proper, even when an external source
provides that generalization.

## Infinitesimal fibres and formal functions, pp.276–279

Let `f : X -> Y` be projective between Noetherian schemes, let `F` be coherent
on `X`, and let `y : Y`. For `n >= 1`, define

`X_n = X times_Y Spec(O_(Y,y) / m_y^n)`

and let `F_n` be the pullback of `F` to `X_n`. Thus `X_1` is the
scheme-theoretic fibre and every `X_n` has the same underlying topological
space. In a natural-number implementation, stage `n` uses `m_y^(n+1)` so that
stage zero is Hartshorne's `X_1`.

The higher-direct-image base-change map, the affine-target description of
higher direct images, and passage to inverse limits give the natural map

`completion_(m_y) ((R^i f_* F)_y) -> lim_n H^i(X_n,F_n)`.

Theorem 11.1 states that this map is an isomorphism for every `i >= 0`.
Hartshorne embeds `X` in relative projective space, handles finite sums of
twists explicitly, resolves a general coherent sheaf by such a sum, and uses
descending induction on cohomological degree. The failure of restriction to
the thickening to preserve the first kernel is isolated in systems `K_n`.
Artin–Rees, in the form that the induced adic topology on a finite submodule
agrees with its intrinsic adic topology, makes `K_n` pro-zero.

The proof also uses exactness of completion on finite modules and exactness of
inverse limits under the Mittag–Leffler condition. These are distinct inputs:
ordinary left exactness of an inverse limit is insufficient.

Hartshorne's Remark 11.1.1 cites the proper version in EGA III §4. Remarks
11.1.2–3 identify the degree-zero limit with functions on the formal
completion and mention cohomology on the formal scheme. These remarks are
recorded but do not replace the projective source theorem by a proper or
formal-scheme theorem.

Adopted external references are EGA III §4 and Stacks Project §30.20, tag
`02O7`, especially Theorem 30.20.5, tag `02OC`.

## Applications of formal functions, pp.279–281

Corollary 11.2 sets

`r = max { dim X_y | y in Y }`

and proves `R^i f_* F = 0` for `i > r`. Projectivity supplies a uniform finite
bound on fibre dimension. The proof combines formal functions with
cohomological vanishing above the dimension of the underlying space and uses
coherence plus faithful maximal-adic completion to recover a zero stalk.

Corollary 11.3 assumes `f_* O_X -> O_Y` is an isomorphism and proves every
fibre is connected. A disconnected fibre yields nontrivial complementary
idempotents on every infinitesimal fibre, hence a forbidden product
decomposition of the completed local ring.

Corollary 11.4 assumes `f : X -> Y` is a birational projective morphism of
Noetherian integral schemes and `Y` is normal. Coherence of `f_*O_X` makes its
sections finite over an affine target; birationality places them in the common
function field, and normality forces `f_*O_X = O_Y`. Corollary 11.3 then gives
connected fibres. This is Hartshorne's connected-fibre form of Zariski's Main
Theorem, not Mathlib's modern factorization of a quasi-finite separated map as
an open immersion followed by an integral map. Hartshorne cites Zariski [2],
“A simple analytical proof of a fundamental property of birational
transformations,” *PNAS* 35 (1949), 62–66.

Corollary 11.5 constructs the Stein factorization

`X -> Spec_Y(f_*O_X) -> Y`.

The second map is finite, while the first is projective and has connected
fibres. Stacks Project §37.53, tag `03GX`, especially Theorem 37.53.4, tag
`03H0`, is adopted supplementary prior art; the roadmap retains Hartshorne's
projective Noetherian statement.

## Exercise 11 disposition, pp.280–281

- Exercise 11.2 is adopted. A projective morphism with finite fibres is
  finite. It is used in V.1.10 and V.5.2.
- Exercise 11.3 is adopted. For a basepoint-free linear system on a normal
  projective variety that is not composite with a pencil, every member is
  connected. It is anticipated by III Remark 10.9.1.
- Exercise 11.8 is adopted. If `F` is coherent and flat over the target and
  `H^i(X_y,F_y)=0`, then `R^i f_*F` vanishes near `y`. It is used in V.2.4.
- Exercises 11.1 and 11.4 are **OUT**: they have no later running-text
  dependency.
- Exercises 11.5–11.7 are **OUT**. They form the formal Picard/Lefschetz and
  nonalgebraizability chain already recorded as deferred in the II.9 roadmap.

## Cohomology after tensor and finite-free models, pp.281–287

Fix a Noetherian ring `A`, `Y=Spec A`, a projective `f : X -> Y`, and a
coherent `F` flat over `Y`. For every `A`-module `M`, define

`T^i(M) = H^i(X, F tensor_A M)`.

Proposition 12.1 says the `T^i` are additive covariant functors, exact in the
middle, and form a delta functor.

Proposition 12.2 constructs a bounded-above complex `L` of finite free
`A`-modules such that

`H^i(L tensor_A M) ~= T^i(M)`

naturally in every `M`, compatibly with the delta-functor structure. The
algebraic Lemma 12.3 starts with a bounded-above complex `C` whose cohomology
modules are finite, constructs a bounded-above finite-free `L -> C` inducing
cohomology isomorphisms, and shows the same after arbitrary tensor when every
term of `C` is flat. Hartshorne applies it to an affine-cover Čech complex:
flatness of `F` gives flat terms, and projectivity/coherence gives finite
cohomology.

For `W^i(L)=coker(L^(i-1)->L^i)`, Proposition 12.4 identifies left exactness
of `T^i` with projectivity of `W^i` and with a representation
`T^i(M) ~= Hom_A(Q,M)` for a unique finite `Q`. Proposition 12.5 constructs
the natural tensor comparison

`T^i(A) tensor_A M -> T^i(M)`

and identifies right exactness with this map being an isomorphism, equivalently
surjective, for every `M`. Corollary 12.6 identifies exactness with right
exactness plus projectivity of `T^i(A)`. Proposition 12.7 proves the left-,
right-, and exact loci are open on the base.

Stacks Project §30.22, tag `07VJ`, especially Lemma 30.22.1, tag `07VK`, is
adopted modern prior art: it packages `RΓ(X,F)` as a perfect complex commuting
with arbitrary base change. The source-facing roadmap retains Hartshorne's
explicit finite-free complex and elementary functor criteria.

## Semicontinuity, Grauert, and base change, pp.287–291

A function to the integers is upper semicontinuous when it can only increase
under specialization. Example 12.7.2 proves that for coherent `G` on a
Noetherian scheme, the fibre-generator function

`y |-> dim_(k(y)) (G tensor k(y))`

is upper semicontinuous.

Theorem 12.8 assumes `f : X -> Y` projective between Noetherian schemes and
`F` coherent and flat over `Y`. For every `i`,

`y |-> dim_(k(y)) H^i(X_y,F_y)`

is upper semicontinuous. Corollary 12.9 additionally assumes `Y` integral and
this dimension function constant for a fixed `i`; it concludes `R^i f_*F` is
locally free and every residue-field base-change map is an isomorphism.

Examples 12.9.1–2 are retained as consequences: cohomology is constant for a
flat family of integral curves, while the embedded-point degeneration from
III.9.8.4 makes `h^0` and `h^1` jump. Example 12.9.3 invokes Hodge theory over
`C` and is **OUT**.

Proposition 12.10 uses formal functions. Surjectivity of the residue-field
comparison at one point implies right exactness of `T^i` at that point. The
proof first treats finite-length modules, passes to all infinitesimal
quotients, takes inverse limits, and uses faithful exact completion for finite
modules.

Theorem 12.11 states:

1. if `phi^i(y) : (R^i f_*F) tensor k(y) -> H^i(X_y,F_y)` is surjective,
   it is an isomorphism and remains so near `y`;
2. assuming `phi^i(y)` is surjective and `i>0`, surjectivity of
   `phi^(i-1)(y)` is equivalent to local freeness of `R^i f_*F` near `y`.

Hartshorne attributes the analytic semicontinuity theorem to Grauert [1], the
algebraic results to EGA III §7.7, and the simplified proof to Mumford,
*Abelian Varieties*, II §5. Stacks Project §36.32, tag `0BDM`, especially
Lemma 36.32.1, tag `0BDN`, is adopted supplementary modern prior art.

## Exercise 12 disposition, pp.291–292

- Exercise 12.4 is adopted. For a flat projective family with integral fibres
  over an integral finite-type base, two invertible sheaves fibrewise
  isomorphic differ by pullback of an invertible sheaf on the base. It is used
  in IV p.323.
- Exercise 12.5 is adopted. For finite locally free `E` of rank at least two
  on an integral finite-type base, `Pic(P(E)) ~= Pic(Y) times Z`. The rank
  hypothesis repairs Hartshorne's omitted edge case: for rank one the stated
  product with `Z` is false. The exercise is cited in V.2.3.
- Exercise 12.6 is adopted. If `X` is integral projective with
  `H^1(X,O_X)=0` and `T` is connected finite type, possibly nonreduced, then
  restrictions of a line bundle on `X times T` to closed fibres are mutually
  isomorphic and `Pic(X times T) ~= Pic(X) times Pic(T)`. It is contrasted
  with IV Exercise 4.10 and V Exercise 1.6.
- Exercises 12.1–12.3 are **OUT**: no later running-text dependency was found.

## Pinned Mathlib audit

The audited checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). Exact reusable
infrastructure includes:

- `AdicCompletion.map_exact` in
  `Mathlib/RingTheory/AdicCompletion/Exactness.lean`;
- `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` in
  `Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean`;
- `CategoryTheory.Functor.IsMittagLeffler`,
  `isMittagLeffler_of_exists_finite_range`, and
  `surjective_toEventualRanges` in
  `Mathlib/CategoryTheory/CofilteredSystem.lean`;
- `IsFinite.of_isProper_of_locallyQuasiFinite` and
  `Scheme.Hom.exists_isIso_morphismRestrict_toNormalization` in
  `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`;
- `Module.Flat.projective_of_finitePresentation` in
  `Mathlib/RingTheory/Flat/EquationalCriterion.lean`;
- the generic `UpperSemicontinuous` API in
  `Mathlib/Topology/Semicontinuity/Defs.lean`.

The modern scheme-level Zariski Main implementation is recent work by Andrew
Yang in Mathlib PRs #35093 and #35232. It is relevant prior art but not an
exact declaration of Hartshorne Corollary 11.4.

No exact pinned declaration was found for formal functions, completion of a
higher-direct-image stalk, connected-fibre Zariski Main, Stein factorization,
the finite-free cohomology model, coherent fibre-cohomology semicontinuity,
Grauert, cohomology and base change, or the adopted Picard exercises. A
source-shaped wrapper such as Exercise 11.2 must not be marked `mathlib: true`
merely because a stronger upstream theorem proves it.

## Representation blockers

The existing higher-direct-image base-change-map roadmap leaf is
`not_ready: true`: pinned Mathlib has no module-sheaf higher-direct-image API
that determines the natural comparison map. Consequently the formal-functions
comparison-map article is the representation root marked not ready; the
formal-functions theorem and §12.10–12.11 are derivatively blocked through
their DAG edges rather than separately hand-marked.

Further implementation risks, but not unresolved mathematical statements,
are the sheaf/cohomology comparison with algebraic adic completion, the
Artin–Rees pro-zero system, a concrete finite-free tensor-compatible complex,
relative Spec of `f_*O_X`, and the nonreduced-base clause of Exercise 12.6.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Infinitesimal fibres `X_n,F_n` | `cohomology/formal-functions/core/infinitesimal-fibers.md` |
| Formal-functions natural map | `cohomology/formal-functions/core/formal-functions-comparison-map.md` |
| Twist base case | `cohomology/formal-functions/core/formal-functions-projective-twist-case.md` |
| Artin–Rees pro-zero kernel | `cohomology/formal-functions/core/artin-rees-pro-zero-kernel.md` |
| Theorem 11.1 | `cohomology/formal-functions/core/theorem-on-formal-functions.md` |
| Faithful finite completion | `cohomology/formal-functions/core/maximal-adic-completion-faithful-finite.md` |
| Corollary 11.2 | `cohomology/formal-functions/applications/higher-direct-image-vanishing-fiber-dimension.md` |
| Corollary 11.3 | `cohomology/formal-functions/applications/direct-image-units-connected-fibers.md` |
| Normal birational pushforward | `cohomology/formal-functions/applications/birational-normal-pushforward-structure-sheaf.md` |
| Corollary 11.4 | `cohomology/formal-functions/applications/zariski-main-connected-fibers.md` |
| Corollary 11.5 | `cohomology/formal-functions/applications/stein-factorization.md` |
| Exercises 11.2, 11.3, 11.8 | `cohomology/formal-functions/applications/` |
| Propositions 12.1–12.7 | `cohomology/semicontinuity/finite-free-complex/` |
| Example 12.7.2, Theorem 12.8 | `cohomology/semicontinuity/foundations/` |
| Corollary 12.9, Proposition 12.10, Theorem 12.11 | `cohomology/semicontinuity/theorems/` |
| Exercises 12.4–12.6 | `cohomology/semicontinuity/exercises/` |
