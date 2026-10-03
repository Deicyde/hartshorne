# Hartshorne II.9, *Formal Schemes*

Robin Hartshorne, *Algebraic Geometry*, Chapter II, §9, printed pp.190–200.
In the repository PDF, zero-based PDF index equals printed page plus 14.

## Source boundary and adoption policy

The section begins on printed p.190 after Exercise 8.8. The adopted §9
formalization boundary runs through printed p.200: the running definitions and
results end with Corollary 9.9 and Remark 9.9.1 on p.199, and the explicitly
delegated Exercise 9.3(a,b) and Exercise 9.4 continue the adopted chain through
p.200. The remaining exercise material continues beyond this boundary. Remark 9.9.1
delegates closure of coherent formal modules under extensions to Exercise 9.4,
whose proof in turn delegates the affine exactness step to Exercise 9.3.

Exercises 9.1–9.2 and 9.5 are not cited or used later and are not targets.
Exercise 9.6 is deferred: it is used only by the exercise-only chain beginning
at III, Exercise 11.5, rather than by later running text. The nonalgebraizable
line bundle and nonglobally-generated formal vector bundle of III, Exercise
11.7 remain forward pathology notes, not dependency edges in this DAG.

Throughout the roadmap, natural-number indexing is shifted: the `n`th
infinitesimal neighbourhood is cut out by `I^(n+1)`. Thus stage zero is
`O_X/I`, namely the original closed subscheme `Y`, rather than the zero ring
arising from quotienting by `I^0 = A`. This preserves Hartshorne's systems
indexed by positive integers.

## Inverse systems and sheaf limits

- **Definitions and Proposition 9.1, pp.190–192.** Hartshorne defines inverse
  systems of abelian groups, their limits, exact sequences of systems, and the
  Mittag–Leffler condition. An ML system can be replaced by its stable-image
  system, whose transition maps are surjective and whose limit is unchanged.
  ML descends to a quotient system, and a levelwise short exact sequence stays
  exact after inverse limits when its kernel system is ML.
- **Examples 9.1.1–9.1.2, p.192.** Surjective transition maps imply ML, as does
  the descending chain condition on every term.
- **Proposition 9.2 and Caution 9.2.1, pp.192–193.** Inverse limits of sheaves
  of abelian groups exist and are computed sectionwise. This is already the
  roadmap leaf `schemes/sheaves/limits-of-sheaves`; §9 reuses that node rather
  than duplicating it. Right exactness can fail in the sheaf category even for
  surjective transition maps, so subsequent arguments pass to sections.

## Adic completion

- **Definitions, p.193.** For an ideal `I` of a ring `A`, define
  `Ahat = lim_n A/I^(n+1)` and, for an `A`-module `M`,
  `Mhat = lim_n M/I^(n+1)M`.
- **Theorem 9.3A(a–d), pp.193–194.** For Noetherian `A`, completed powers are
  the kernels of the projections, the quotient of the completion recovers
  `A/I^(n+1)`, finite-module completion is ordinary tensor product with
  `Ahat`, completion is exact on finite modules, and `Ahat` is Noetherian.
- **Theorem 9.3A(e), pp.193–194.** A surjective compatible system of finite
  `A/I^(n+1)`-modules with the prescribed kernels is induced by a finite
  `Ahat`-module. Hartshorne cites Bourbaki for this effectivity statement.

The suffix `A` marks background algebra quoted without proof. Hartshorne cites
Atiyah–Macdonald, pp.108–109 and p.113, for (a–d), and Bourbaki, Chapter III,
§2, no.11, Proposition and Corollary 14, for (e).

## Formal completions and formal schemes

- **Introductory discussion, p.190.** The thickenings cut out by successive
  ideal powers encode the infinitesimal neighbourhoods of a closed subvariety.
  Their inverse limit is the formal neighbourhood inside the ambient scheme.
- **Definitions and Remark 9.3.1, p.194.** For a Noetherian scheme `X` and a
  closed subscheme `Y` with module ideal sheaf `I`, the completion has space
  `|Y|` and structure sheaf `lim O_X/I^(n+1)`. It is a locally ringed space,
  depends only on the closed support, and has completed affine section rings.
  For coherent `F`, its completion is `lim F/I^(n+1)F`.

Mathlib's `Scheme.IdealSheafData` is compatible affine-open ideal data, not
definitionally a subobject of the structure sheaf in `X.Modules`. The formal
completion construction therefore depends on the existing project bridge
between ideal data and module ideal sheaves; the roadmap must not take powers,
quotients, or completed modules directly on `IdealSheafData` as if the two
representations were identical.

- **Definition, p.194.** A Noetherian formal scheme is a locally ringed
  space with a finite open cover by completions of Noetherian schemes along
  closed subschemes. Morphisms are morphisms of locally ringed spaces.
  Coherent modules are locally completions of coherent modules on such charts.
  This is Hartshorne's plain locally ringed-space definition; no topology on
  the section rings is added.
- **Examples 9.3.2–9.3.4 and affine formal schemes, p.195.** Scheme completions are algebraizable formal
  schemes, an ordinary Noetherian scheme is recovered by completing along
  itself, and completion at a closed point is the one-point locally ringed
  space with completed local ring.

The existence of nonalgebraizable formal schemes mentioned in Example 9.3.2
is `OUT`: it is contextual evidence that algebraizability is restrictive, not
a definition or result used by the §9 formalization.

The roadmap introduces `Spf_I(A)` only as project notation for the completion
of `Spec A` along `V(I)`. Hartshorne does not introduce this notation. A
separate bridge compares it with the usual formal spectrum of the completed
adic ring; no statement about continuous morphisms of topological rings is
attributed to Hartshorne.

That bridge is project-authored with the following explicit assumptions. For
Noetherian `A` and `I`, form `Ahat` and `Ihat = I Ahat`; take the usual EGA
formal spectrum on the open-prime space of the `Ihat`-adic topological ring;
identify that space with `V(I)`; identify its quotient structure sheaves with
the sheaves of `Ahat/Ihat^(n+1)`; and then forget section topologies. The
quotient isomorphisms with `A/I^(n+1)` produce the comparison with
Hartshorne's inverse-limit locally ringed space. These assumptions are proved
or cited by the bridge leaf rather than built into Hartshorne's definition.

## Affine formal schemes and ideals of definition

- **Proposition 9.4, pp.195–196.** On an affine formal completion, the
  completed ideal is an ideal sheaf, its power quotients recover the ordinary
  thickening sheaves, finite-module completion is the ordinary sheaf tensor
  `Mtilde tensor O_hat`, and completion is exact on finite modules. This is an
  ordinary tensor product of module sheaves, not a newly invented completed
  tensor product.
- **Definition and Proposition 9.5, pp.196–197.** An ideal of definition has
  full support and Noetherian scheme quotient. Any two ideals of definition
  are adically cofinal; there is a unique largest one, characterized by its
  reduced quotient; and every positive power remains an ideal of definition.

## Coherent modules on formal schemes

- **Proposition 9.6, pp.197–198.** A coherent formal module is the inverse
  limit of its coherent reductions. Conversely, a compatible system of
  coherent modules with surjective maps and the prescribed kernels has a
  coherent inverse limit and the expected reductions.
- **Theorem 9.7, p.198.** For a complete Noetherian affine adic ring, finite
  modules and coherent modules on the affine formal scheme are equivalent via
  completion and global sections; both functors are exact.
- **Corollary 9.8, p.198, and Corollary 9.9, p.199.** Completion of coherent sheaves on an
  ordinary Noetherian scheme is exact and satisfies the quotient and ordinary
  tensor comparisons. Kernels, cokernels, and images of coherent formal
  modules are coherent.

## Adopted exercises and deferred material

- **Exercise 9.3(a,b), pp.199–200.** Affine formal global sections preserve a
  short exact sequence when the kernel is coherent. The proof applies affine
  scheme exactness on every thickening and then Proposition 9.1, Proposition
  9.2, and Proposition 9.6.
- **Exercise 9.4, p.200.** Extensions of coherent modules on a Noetherian
  formal scheme are coherent. Remark 9.9.1 explicitly cites this result.
- **Exercise 9.6, beginning after the adopted p.200 boundary, deferred.** The Picard comparison with the inverse
  system of thickenings is not part of this §9 DAG. Its later use is confined
  to III, Exercise 11.5 and the associated exercise chain.
- **III, Exercise 11.7, forward note (`OUT`).** Formal completions can carry
  nonalgebraizable invertible sheaves and coherent locally free sheaves whose
  twists are never globally generated. These are warnings against importing
  ordinary projective-scheme intuition, not current theorem dependencies.

## Pinned Mathlib audit

The pinned checkout is Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`.

Exact stable primitives include:

- `CategoryTheory.Functor.IsMittagLeffler`,
  `CategoryTheory.Functor.toEventualRanges`,
  `CategoryTheory.Functor.toEventualRangesSectionsEquiv`, and
  `CategoryTheory.Functor.surjective_toEventualRanges` in
  `Mathlib/CategoryTheory/CofilteredSystem.lean`;

- `AdicCompletion`, `AdicCompletion.transitionMap`, and
  `AdicCompletion.eval` in
  `Mathlib/RingTheory/AdicCompletion/Basic.lean`;
- `AdicCompletion.evalₐ` and `AdicCompletion.surjective_evalₐ` in
  `Mathlib/RingTheory/AdicCompletion/Algebra.lean`;
- `AdicCompletion.pow_smul_top_eq_ker_eval` and
  `AdicCompletion.isAdicComplete` in
  `Mathlib/RingTheory/AdicCompletion/Completeness.lean`;
- `AdicCompletion.map_surjective`, `AdicCompletion.map_injective`, and
  `AdicCompletion.map_exact` in
  `Mathlib/RingTheory/AdicCompletion/Exactness.lean`;
- `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` and the flatness
  instance in `Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean`;
- `CategoryTheory.Sheaf.isSheaf_of_isLimit` and the limit-creation instance in
  `Mathlib/CategoryTheory/Sites/Limits.lean`.

The cofiltered-system API supplies the set-valued ML predicate and
stable-eventual-range machinery. It does not supply Hartshorne's exactness
theorem for inverse systems of abelian groups; the file explicitly leaves the
general nonempty-limit lemma corresponding to Stacks tag `0597` as a TODO.
No pinned implementation was found for Noetherianity of a general adic
completion, compatible-system effectivity, scheme formal completion, formal
schemes, `Spf`, ideals of definition, or coherent formal modules.

Mathlib pull request
[`#38331`](https://github.com/leanprover-community/mathlib4/pull/38331),
"AdicCompletion of Noetherian ring is Noetherian", is open and modifies
`Mathlib/RingTheory/AdicCompletion/Noetherian.lean`. It is prior work, not part
of the pinned checkout and therefore not asserted as formalized here.

## External proof sources and unresolved obligations

- Stacks tags `0595`–`0598` cover the ML definition, stable images, nonempty
  inverse limits, and exactness under ML.
- Stacks tags `05GG` and `031C` cover completed powers and quotient recovery.
- Stacks tags `00MA` and `00MB` cover finite-module tensor comparison,
  exactness, and flatness over a Noetherian ring.
- Stacks tag `0316` proves that the completion of a Noetherian ring is
  Noetherian.
- Stacks tag `0319` proves invariance under cofinal adic filtrations.
- Hartshorne's proof of Proposition 9.5 on printed p.197 uses
  II, Exercise 2.18(a): an empty principal open detects nilpotence.
- Stacks tag `031D` is useful for proving finiteness of a complete module from
  its reduction, but it is not a verbatim source for Theorem 9.3A(e).
  Until the cited Bourbaki passage is inspected, the compatible-system
  effectivity leaf remains `not_ready`.
- Stacks §87.2, tag `0AHY`, describes the usual topological-ring `Spf` and EGA
  formal schemes. Its comparison with Hartshorne's plain locally ringed-space
  definition is a representation bridge, not an exact source match.

## Later-consumer audit

| Later consumer | Precise §II.9 input | Disposition |
|---|---|---|
| III.1, Example 1.0.7 | Corollary 9.9: kernels, cokernels, and images of coherent formal modules are coherent, so they form an abelian category | Decomposed by `coherent-formal-abelian-closure` |
| III.9, Example 9.1.2 | Theorem 9.3A(b,c): finite-module completion is tensor with `Ahat` and is exact, hence `Ahat` is flat over `A` | Exact pinned adic leaves plus the existing Mathlib flatness instance |
| III.11, Theorem 11.1 and Remark 11.1.2 | Proposition 9.1 and Examples 9.1.1–2 for exact inverse limits; Theorem 9.3A(c) for exact completion; Proposition 9.2 for sectionwise limits; formal completion and the Corollary 9.8 tensor comparison for the `i = 0` interpretation | Decomposed across all four §II.9 milestones; Proposition 9.2 reuses the existing sheaf-limit leaf |
| III.12, Proposition 12.10 | Proposition 9.1 and Example 9.1.2: finite-length kernel systems are ML, so surjectivity passes to their inverse limit | Decomposed in the inverse-systems milestone |
| V.3, Proposition 3.4 | Formal completion at the exceptional fibre, its infinitesimal reductions, and Theorem 9.3A/Corollary 9.8 comparisons used through the theorem on formal functions | Decomposed in the adic, formal-neighbourhood, and coherent-module milestones |
| V.5, Theorem 5.7 | Remark 9.3.1: powers of the point ideal pulled back to the source are cofinal with powers of the contracted-curve ideal, so they define the same completion | Decomposed by `formal-completion-support-invariant` |
| Remark 9.9.1 | Exercise 9.3(a,b) and Exercise 9.4, giving affine exactness and closure under extensions | Adopted through the delegated proof chain ending on p.200 |
| III, Exercise 11.5 | Exercise 9.6, the Picard inverse-limit comparison | Deferred exercise-only chain; no current DAG edge |
| Example 9.3.2 and III, Exercise 11.7 | Existence of nonalgebraizable formal schemes and formal line bundles | `OUT`; contextual pathology, not theorem leaves |
