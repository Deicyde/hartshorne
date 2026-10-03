# Hartshorne III.8, higher direct images of sheaves

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter III, §8. The section runs from printed p.250 through p.253 (PDF pages
265–268): the definition and Proposition 8.1 begin on p.250, Propositions
8.2–8.6 occupy p.251, Propositions 8.7–8.8 and Exercises 8.1–8.2 are on
p.252, and Exercises 8.3–8.4 precede §9 on p.253. Page references below are
printed pages.

## Adopted boundary

The roadmap adopts all running definitions, propositions, corollaries, and
Theorem 8.8. Under the strict exercise policy it adopts only Exercise 8.1,
because its acyclic Leray comparison is cited later and is needed as a stable
interface between higher direct images and ordinary cohomology. Exercises
8.2–8.4 are outside this roadmap boundary.

The later “see also” citations to excluded exercises are evidence only, not
dependency edges. Exercise 8.3 is cited in V, Exercise 5.3, printed p.419.
Exercise 8.4 is cited in V, Corollary 2.5, printed p.371, and after V, Lemma
2.10, printed p.374. These citations do not adopt those exercises. The
retained Exercise 8.1 is used in V, Lemma 2.4, printed p.371, V, Proposition
3.4, printed pp.387–388, and V, Exercise 5.3, printed p.419.

## Definition and local description, printed pp. 250–251

For a continuous map `f : X -> Y`, Hartshorne defines `R^i f_*` as the right
derived functors of direct image on abelian sheaves. Direct image is right
adjoint to inverse image, hence preserves finite limits and is left exact;
this is the source-shaped categorical bridge needed for the degree-zero
right-derived comparison. Proposition 8.1
identifies `R^i f_* F` with the sheaf associated to the presheaf

`V |-> H^i(f^{-1}(V), F|_{f^{-1}(V)})`.

The proof compares two universal delta functors. In degree zero both are
direct image. For an injective abelian sheaf `I`, its restriction to every
open `f^{-1}(V)` is injective by III.6.1, so both positive-degree functors
vanish. Corollary 8.2 restricts this formula to an open subset of the base.
Corollary 8.3 says that a flasque sheaf has vanishing positive higher direct
images, because its restrictions to open subsets remain flasque.

Pinned Mathlib defines `Sheaf.cohomologyPresheaf` and `Sheaf.H'` in
`Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`, but that file
explicitly leaves as TODO the comparison between cohomology on an object and
cohomology of the restricted sheaf on its over-site. The roadmap therefore
records that comparison as a separate supporting result rather than treating
Proposition 8.1 as definitional. That bridge must also identify the free
abelian sheaf on the representable open with extension by zero of the
constant sheaf `Z` on the open. Independently, restriction of injective
abelian sheaves is the direct specialization of Hartshorne III.6.1 obtained
by viewing abelian sheaves as modules over the constant sheaf `Z`. These two
facts are recorded explicitly and are not inferred from the site-cohomology
TODO.

## Module-valued higher direct images, printed p. 251

Proposition 8.4 says that for a morphism of ringed spaces the same functors
can be computed as the right derived functors of direct image in the category
of module sheaves. An injective module sheaf is flasque as an underlying
abelian sheaf, hence is acyclic for abelian-sheaf direct image. This both
supplies the comparison and preserves the natural module structure on higher
direct images.

The project-authored Lean specification keeps the two models explicit:
degreewise `Functor.rightDerived` on abelian sheaves for 8.1–8.3, and
degreewise `Functor.rightDerived` on a project ringed-space
`SheafOfModules` interface from 8.4 onward. It asks
for a natural comparison after forgetting module structure. It does not use
`Functor.rightDerivedFunctorPlus`: the pinned implementation states that it
has not yet been made triangulated or connected to the existing degreewise
right-derived functors.

Pinned Mathlib's scheme-specific `Scheme.Modules` wrapper does not by itself
state Proposition 8.4 for arbitrary ringed spaces. The comparison remains
not ready until the project fixes the ringed-space module category, its
forgetful functor to abelian sheaves, the universe parameters, and
compatibility with abelian pushforward.

## Affine targets and quasi-coherence, printed pp. 251–252

Proposition 8.5 takes `X` Noetherian, `Y = Spec A`, and `F` quasi-coherent,
and gives natural isomorphisms

`R^i f_* F ~= (H^i(X,F))~`.

For `i=0` this is the affine tilde/global-sections equivalence. In positive
degrees Hartshorne works inside quasi-coherent modules: both sides are delta
functors, and a quasi-coherent sheaf embeds in a flasque quasi-coherent sheaf
by III.3.6, making both sides effaceable. Corollary 8.6 localizes this result
on the target and concludes that `R^i f_* F` is quasi-coherent for any
morphism from a Noetherian scheme and any quasi-coherent `F`.

Proposition 8.7 assumes `f : X -> Y` is a morphism of separated Noetherian
schemes, `F` is quasi-coherent, and `U` is an affine open cover of `X`. It
identifies

`R^p f_* F ~= h^p(f_* C^.(U,F))`.

After restricting to an affine open of `Y`, the intersections used in the
Čech resolution remain affine, so III.4.5 and Proposition 8.5 identify the
two sides.

## Projective finiteness and vanishing, printed p. 252

Theorem 8.8 assumes a projective morphism of Noetherian schemes, a relatively
very ample invertible sheaf `O_X(1)`, and a coherent module `F`. It proves:

1. for `n` sufficiently large, the adjunction map
   `f^* f_* F(n) -> F(n)` is surjective;
2. every `R^i f_* F` is coherent;
3. for `i>0` and `n` sufficiently large, `R^i f_* F(n)=0`.

All three assertions are local on the Noetherian target. Proposition 8.5
reduces them respectively to II.5.17, III.5.2(a), and III.5.2(b). The three
parts are separate roadmap leaves because each has a distinct completion
criterion and downstream role.

Remark 8.8.1 cites EGA III, 3.2.1 for coherence of higher direct images under
a proper morphism. This stronger result is deferred. It is not part of the
projective theorem leaf and no claim of proper pushforward coherence is made.

## Retained Exercise 8.1, printed p. 252

If `R^q f_* F=0` for every `q>0`, Exercise 8.1 asks for natural isomorphisms

`H^p(Y,f_*F) ~= H^p(X,F)`.

Hartshorne identifies this as the degenerate case of the Leray spectral
sequence and cites Godement, II.4.17.1. A full Leray spectral sequence is not
adopted here. The project-authored proof specification instead chooses an
injective resolution `F -> I^.`. Inverse image of abelian sheaves is exact,
so its right adjoint `f_*` preserves injectives. The complex `f_*I^.`
computes `R^q f_*F`; the vanishing hypothesis and the degree-zero comparison
make it an injective resolution of `f_*F`. The natural identity
`Gamma(Y,f_*I)=Gamma(X,I)` then gives the desired comparison in every degree.
Godement remains the cited external provenance for the general spectral
sequence, not a dependency of this smaller result.

## Pinned Mathlib prior art

The audited checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). Exact useful
primitives include:

- `CategoryTheory.Functor.rightDerived`,
  `InjectiveResolution.isoRightDerivedObj`,
  `Functor.isZero_rightDerived_obj_injective_succ`, and
  `Functor.rightDerivedZeroIsoSelf` in
  `Mathlib/CategoryTheory/Abelian/RightDerived.lean`;
- `TopCat.Sheaf.pushforward`, `TopCat.Sheaf.pullback`, and
  `pullbackPushforwardAdjunction` in
  `Mathlib/Topology/Sheaves/Functors.lean`;
- `TopCat.Sheaf.IsFlasque.pushforward_isFlasque` in
  `Mathlib/Topology/Sheaves/Flasque.lean`;
- `Scheme.Modules.pushforward`, `pushforward_obj_obj`, `pushforwardComp`,
  `restrictFunctor`, `restrictFunctorComp`, and
  `restrictFunctorIsoPullback` in
  `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`;
- `Sheaf.H`, `Sheaf.functorH`, `Sheaf.cohomologyPresheaf`, and `Sheaf.H'`
  in `Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`;
- `CategoryTheory.cechComplexFunctor` in
  `Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean`; and
- `tilde.functor`, `moduleSpecΓFunctor`, `tilde.toTildeΓNatIso`, and
  `isQuasicoherent_iff_isIso_fromTildeΓ` in
  `Mathlib/AlgebraicGeometry/Modules/Tilde.lean`.

These are implementation prior art, not exact formalizations of any whole
leaf below. No exact pinned declaration was found for higher direct images,
the open-object/restricted-sheaf cohomology comparison, Proposition 8.1, the
module/abelian comparison, higher quasi-coherent pushforward, relative Čech
calculation, projective coherent higher pushforward, relative Serre
vanishing, or the acyclic Leray comparison. Consequently no leaf in this
chapter is marked `mathlib: true`.
