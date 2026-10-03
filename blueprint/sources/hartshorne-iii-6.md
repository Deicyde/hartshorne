# Hartshorne III.6, Ext groups and sheaves

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter III, §6. The section begins on printed p.233 (zero-based PDF index
247), after Exercise 5.10, and ends on printed p.239 (index 253), where §7
begins. Page references below are printed pages.

## Boundary and the three Ext models

Hartshorne works on a ringed space `(X,O_X)` in the abelian category of
`O_X`-modules. For fixed `F`, global `Hom_X(F,-)` takes values in abelian
groups, while sheaf `Hom`, written `𝓗om_X(F,-)`, takes values in
`O_X`-modules. Their right derived functors are different objects:

- `Ext^i_X(F,G)` is a group;
- `𝓔xt^i_X(F,G)` is an `O_X`-module sheaf;
- a derived-category `RHom` or internal `R𝓗om` packages all degrees at once.

Pinned Mathlib defines global Ext as shifted morphisms in a derived category,
after choosing an explicit universe `w` and a
`CategoryTheory.HasExt.{w} (Scheme.Modules X)` instance, and compares it with
an injective-resolution Hom complex. It does not define
the internal derived Hom of module sheaves or Hartshorne's sheaf Ext. There is
no general isomorphism `Ext^i_X(F,G) ≅ Γ(X,𝓔xt^i_X(F,G))`: Proposition 6.9
gives an eventual twisted comparison, and Remark 6.9.1 points to a
local-to-global spectral sequence.

## Definitions and restriction, printed pp.233–234

The opening definition makes global and sheaf Ext the right derived functors
of the two Hom functors. Thus degree zero is Hom, positive Ext into an
injective vanishes, and short exact sequences in the second variable give the
usual covariant long exact sequences for both global and sheaf Ext.

Lemma 6.1 says that the restriction of an injective `O_X`-module to an open
subset `U` is injective as an `O_U`-module. Hartshorne uses open extension by
zero and its adjunction with restriction.

Proposition 6.2 gives natural restriction isomorphisms
`𝓔xt^i_X(F,G)|_U ≅ 𝓔xt^i_U(F|_U,G|_U)`. Proposition 6.3 identifies
`𝓔xt^0_X(O_X,G)` with `G`, makes its higher sheaf Ext vanish, and identifies
`Ext^i_X(O_X,G)` with `H^i(X,G)`.

## Exact sequences and locally free resolutions, printed pp.234–235

Proposition 6.4 gives contravariant long exact sequences in the first
variable, both for global Ext and sheaf Ext. For sheaf Ext, exactness of
`𝓗om(-,J)` for injective `J` is checked after restriction and uses Lemma 6.1.

Proposition 6.5 says that a resolution of `F` by finite-rank locally free
sheaves computes `𝓔xt^i_X(F,G)` by the cohomology sheaves of
`𝓗om(L_.,G)`. Example 6.5.1 uses II.5.18 to obtain such resolutions for
coherent sheaves on Noetherian quasi-projective schemes. Caution 6.5.2 warns
that the category of sheaves need not have enough projectives; Exercise 6.4
states a separate first-variable universal property under enough locally
frees.

Lemma 6.6 says that `L ⊗ J` is injective when `L` is finite locally free and
`J` is injective. Its proof uses the tensor–Hom adjunction from II, Exercise
5.1.

## Tensor, stalk, and projective comparison, printed pp.235–236

Proposition 6.7 gives natural tensor-dual isomorphisms
`Ext^i(F⊗L,G) ≅ Ext^i(F,L∨⊗G)` and the analogous isomorphisms for sheaf Ext,
for finite locally free `L`.

For a Noetherian scheme and coherent `F`, Proposition 6.8 identifies the
stalk `𝓔xt^i_X(F,G)_x` with module Ext
`Ext^i_{O_{X,x}}(F_x,G_x)`. Coherence of the first variable is essential even
in degree zero.

Proposition 6.9 considers a projective scheme over a Noetherian ring, a very
ample `O_X(1)`, and coherent `F,G`. For fixed `i`, the natural map

`Ext^i_X(F,G(n)) → Γ(X,𝓔xt^i_X(F,G(n)))`

is an isomorphism for all sufficiently large `n`. The proof starts with
`F=O_X`, passes to finite locally free `F` by Proposition 6.7, and then uses a
locally free cover, both long exact sequences, Serre vanishing, and Exercise
5.10 to dimension-shift.

Remark 6.9.1 says that the general relation is a spectral sequence and cites
Grothendieck [1] and Godement [1, II, 7.3.3]. For the derived inputs
`K=F[0]` and `L=G[0]`, `K` is bounded above and `L` is bounded below, so the
adopted specification is the convergent
first-quadrant spectral sequence
`E_2^{p,q}=H^p(X,𝓔xt^q_X(F,G))⇒Ext_X^{p+q}(F,G)`; its total-degree-`q`
edge is the natural map from global Ext to global sections of sheaf Ext.
Stacks Project, tag
[0BQP](https://stacks.math.columbia.edu/tag/0BQP), is the adopted modern
locator for this local-to-global Ext spectral sequence.

## Quoted homological algebra, printed pp.236–237

- Proposition 6.10A characterizes projective modules by vanishing of
  `Ext^1(M,-)` and characterizes `pd(M)≤n` by vanishing of `Ext^i(M,-)` for
  every `i>n`. Hartshorne cites Matsumura [2], pp.127–128.
- Proposition 6.11A says that a regular local ring `A` has global dimension
  `dim A`, more precisely `pd_A(M)≤dim A` for every module and
  `pd_A(A/m)=dim A`. Hartshorne cites Matsumura [2], Theorem 42, p.131.
- Proposition 6.12A is the Auslander–Buchsbaum equality
  `pd_A(M)+depth_A(M)=dim A` for a finite module over a regular local ring.
  Hartshorne cites Matsumura [2], p.113, Exercise 4, or Serre [11], IV.D,
  Proposition 21.

The three cited Matsumura/Serre passages have not yet been inspected directly.
Accordingly the regular-local global-dimension, residue-field, and
Auslander–Buchsbaum leaves remain source-blocked; the generic Ext criterion is
already supplied exactly by pinned Mathlib.

## Adopted exercises, printed pp.237–238

- Exercise 6.1 classifies short exact extensions of `F''` by `F'` by
  `Ext^1(F'',F')`, sending an extension to the connecting image of the
  identity. The extension classes are the quotient of short exact short
  complexes with fixed endpoints by endpoint-identity isomorphisms; no
  Baer-sum compatibility is included. Hartshorne cites Hilton–Stammbach [1],
  Chapter III. It is used in
  V.2.11.6 and V.2.12 (printed pp.375–376).
- Exercise 6.3 proves that `𝓔xt^i(F,G)` is coherent when `F,G` are coherent,
  and quasi-coherent when `F` is coherent and `G` is quasi-coherent. It is
  used in III.7.3 (printed p.241).
- Exercise 6.6 strengthens Proposition 6.10A over a regular local ring: for a
  finite module it suffices to test all positive Ext, or all Ext above a
  bound, against `A` itself. It is used in III.7.6 (printed pp.243–244).

## Excluded exercises, printed pp.237–239

Exercises 6.2, 6.4, 6.5, and 6.7 are outside the agreed later-use scope.
Exercises 6.8 and 6.9 form an optional Kleiman/Borel–Serre chain culminating
in `K_1(X) ≅ K(X)` for regular schemes; no later numbered result invokes that
chain, so it is not silently adopted. Exercise 6.10's finite-flat duality
chain is also excluded from this §6 expansion; adopting it later requires its
own scope and proof-source decision.

## Later use of running results

- III.7.3 uses Exercise 6.3, Proposition 6.7, and Proposition 6.9.
- III.7.6–7.7 use Propositions 6.3, 6.7–6.10A, 6.12A, and Exercise 6.6.
- III.7.11 uses Proposition 6.5.
- III.8.1 uses Lemma 6.1.
- V.2.11.6 uses Exercise 6.1 and Propositions 6.3 and 6.7; V.2.12 again uses
  Exercise 6.1.

## Pinned Mathlib audit

The audited checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). Exact generic
primitives are:

- `CategoryTheory.Abelian.Ext`, `CategoryTheory.Abelian.Ext.addEquiv₀`, and
  `CategoryTheory.Abelian.extFunctor` in
  `Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean`;
- `CategoryTheory.InjectiveResolution.extAddEquivCohomologyClass` in
  `Mathlib/CategoryTheory/Abelian/Injective/Ext.lean`;
- `CategoryTheory.Abelian.Ext.eq_zero_of_injective` and
  `CategoryTheory.hasExt_of_enoughInjectives` in
  `Mathlib/Algebra/Homology/DerivedCategory/Ext/EnoughInjectives.lean`;
- `CategoryTheory.Abelian.Ext.covariantSequence`,
  `covariantSequence_exact`, `contravariantSequence`, and
  `contravariantSequence_exact` in
  `Mathlib/Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean`;
- `CategoryTheory.hasProjectiveDimensionLT_iff` and
  `projective_iff_subsingleton_ext_one` in
  `Mathlib/CategoryTheory/Abelian/Projective/Dimension.lean`.

Partial primitives are
`CategoryTheory.ShortComplex.ShortExact.extClass` for Exercise 6.1,
`ModuleCat.finite_ext` for Exercise 6.3, and
`SheafOfModules.IsLocallyFree` for locally free terminology. The root-level
`Ext R C n` in `Mathlib/CategoryTheory/Abelian/Ext.lean` requires enough
projectives and is not the chosen model.

No exact pinned declaration was found for module-sheaf internal Hom as a
left-exact endofunctor, sheaf Ext, internal derived Hom, open restriction of
injectives, restriction/stalk/tensor comparisons, Proposition 6.9, the
local-to-global spectral sequence, regular-local global dimension,
Auslander–Buchsbaum, or the three adopted exercises.

## Remaining source obligations

The project must fix the internal-Hom complex and cohomology-sheaf conventions
used to compare tag 0BQP with the chosen sheaf-Ext model, and construct the
edge map in Proposition 6.9 compatibly with them. It must also choose and
propagate one `HasExt` universe for `Scheme.Modules X`, lift open extension by
zero and its adjunction to module sheaves, encode finite rank in the locally
free API, construct the extension setoid, and expand the hinted
descending-induction proof of Exercise 6.6. The quoted Matsumura and Serre
passages must be checked directly before the three source-blocked
regular-local leaves are made ready.
