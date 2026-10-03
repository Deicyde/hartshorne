# Hartshorne III.1–2 source notes

The source is the repository PDF, *Algebraic Geometry* (1977). The scope is
printed pp. 202–213 (PDF indices 216–227): running text in §§1–2 and only the
exercises later cited or used. Page references below are printed pages.

## Derived-functor foundations, printed pp. 202–206

Hartshorne defines abelian categories, cochain complexes, cohomology objects,
homotopies, additive and exact functors, injectives, injective resolutions, and
right derived functors. Theorem 1.1A (pp. 204–205) gives functoriality,
independence of resolutions, `R⁰F ≅ F`, the natural long exact sequence, and
higher vanishing on injectives. Proposition 1.2A (p. 205) says an `F`-acyclic
resolution computes `RⁱF`. Theorem 1.3A and Corollary 1.4 (p. 206) give the
effaceability criterion for a universal delta functor and characterize derived
functors by that universal property.

Hartshorne explicitly presents this material without proofs. The following
source stack, listed by Hartshorne on printed p. 202, is adopted for the quoted
homological-algebra results; individual roadmap nodes route to the relevant
locator below.

## Adopted homological-algebra source stack

- Peter Freyd, *Abelian Categories* (1964), especially Chapter 7 on the full
  embedding theorem, is Hartshorne's p. 203 structural reference. It is
  recorded for provenance; the roadmap uses Mathlib's categorical
  constructions directly rather than reducing proofs to module categories.
- Roger Godement, *Topologie algébrique et théorie des faisceaux*, Hermann,
  Paris (1958), Chapter I, §§1.1–1.8, 2.1–2.4, and 5.1–5.3: complexes,
  injective resolutions, derived functors, acyclic resolutions, and sheaf
  cohomology.
- Peter J. Hilton and Urs Stammbach, *A Course in Homological Algebra*,
  Graduate Texts in Mathematics 4, Springer-Verlag (1970), Chapters II, IV,
  and IX; Chapter IV, §4.4 is the adopted comparison theorem from an arbitrary
  resolution to an injective resolution, unique up to homotopy.
- Alexander Grothendieck, “Sur quelques points d'algèbre homologique,”
  *Tohoku Mathematical Journal* 9 (1957), 119–221, Chapter II, §§1–3;
  II.2.2.1 is the adopted effaceable-delta-functor criterion.
- Henri Cartan and Samuel Eilenberg, *Homological Algebra*, Princeton
  University Press (1956), Chapters III and V: complexes, resolutions, and
  derived functors.
- Joseph J. Rotman, *Notes on Homological Algebra*, Van Nostrand Reinhold
  Mathematical Studies 26 (1970), §6: injectives and derived functors.

The stack grounds the mathematical statements, but the project has not chosen
a Lean representation of delta functors, so the universal-delta-functor node
remains not ready. Exact pinned-Mathlib constructions are used only on nodes
whose full main result was verified.

## Enough injectives and cohomology, printed pp. 206–208

Proposition 2.1A (p. 206) says every module embeds in an injective module;
Hartshorne cites Godement, *Topologie algébrique et théorie des faisceaux*,
I.1.2.2, and Hilton–Stammbach, *A Course in Homological Algebra*, I.8.3. We
adopt both locators, with pinned Mathlib as the implementation source.
Proposition 2.2 and Corollary 2.3 (p. 207) establish enough injectives for
sheaves of modules and abelian sheaves. Cohomology is then defined as
`Hⁱ(X,-) = RⁱΓ(X,-)`. Lemma 2.4, Proposition 2.5, and Proposition 2.6
(pp. 207–208) show respectively that injective module sheaves are flasque,
flasque abelian sheaves are acyclic, and module-category derived global
sections agree with underlying abelian-sheaf cohomology. Remark 2.6.1 records
the natural `Γ(X,O_X)`-module, and hence base-ring, structure.

Mathlib's `Sheaf.H` is defined as an Ext group from the constant integral
sheaf. It is implementation prior art, not definitionally Hartshorne's `RΓ`.
The roadmap therefore requires a natural comparison between Ext from the
constant integral sheaf and the right-derived global-sections functor,
including the degree-zero identification `Hom(Z_X,F) ≅ Γ(X,F)`. This
comparison is not supplied by the pinned checkout and remains not ready.

## Filtered colimits and closed support, printed pp. 208–210

Theorem 2.7 (p. 208) states that a noetherian topological space of dimension
`n` has `Hⁱ(X,F)=0` for `i>n`. Lemma 2.8 and Proposition 2.9 (p. 209) say
filtered colimits preserve flasqueness and commute with cohomology on a
noetherian space; cohomology therefore commutes with arbitrary direct sums.
Lemma 2.10 (pp. 209–210) identifies cohomology on a closed subspace with the
cohomology of its direct image, viewed as extension by zero.

These arguments adopt the following Chapter II exercises as supporting input:
II.1.11, evaluation of filtered colimits on opens of a noetherian space;
II.1.16(a–e), the flasque-sheaf package; II.1.19(c), the open–closed extension
exact sequence; and II.1.20, the subsheaf and sections with closed support.
They were deferred by the Chapter II source notes and are included here only
where a Chapter III result needs them.

## Grothendieck vanishing proof, printed pp. 210–211

Hartshorne reduces first to irreducible spaces and proves the dimension-zero
irreducible base case. For an irreducible space of dimension `n`, he then
reduces from an arbitrary sheaf to finitely generated subsheaves and finally
to a sheaf generated by one local section, hence a quotient of `Z_U`. For a
nonzero subsheaf `M ⊆ Z_U`, he chooses the least positive integer occurring in
its stalks and asserts that `M|_V ≅ d Z|_V` on a nonempty open `V`; the quotient
is supported on the proper closed subset `closure(U \\ V)`, whose dimension is
strictly less than `n`. The final induction uses
`0 → Z_U → Z → Z_Y → 0`, flasqueness of `Z` on an irreducible space, and the
same proper-closed dimension drop.

The formal dimension convention is project-authored: use Mathlib's
`topologicalKrullDim : WithBot ℕ∞` and state finite-dimensional hypotheses by
an equality `topologicalKrullDim X = n`. A separate bridge proves strict
dimension drop for a proper closed subset of an irreducible noetherian space.
No conversion to an unguarded natural-valued dimension is implicit.

The generic-trivialization assertion is not proved in enough detail to fix its
Lean representation. Until a detailed source or project-authored specification
is adopted, its node is not ready and the final vanishing theorem is blocked by
that dependency.

## Adopted exercises, printed pp. 212–213

Only the following exercises are included.

- Exercise 2.2 (p. 212), cited in III.7: II.1.21(d) identifies the quotient of
  the constant function-field sheaf by `O` with the direct sum of skyscraper
  principal-parts sheaves, and II.1.21(e) proves surjectivity on global
  sections. Together these give a flasque resolution of `O` on `P¹`, hence
  `Hⁱ(P¹,O)=0` for `i>0`.
- Exercise 2.3(a–f) (p. 212), used in III.3.3 and III.4.9: cohomology with
  supports, flasque acyclicity, the localization sequence, and excision.
- Exercise 2.4 (p. 212), used in III.4.9: Mayer–Vietoris for two closed
  supports.
- Exercise 2.7 (p. 213), cited in III.4: `H¹(S¹,Z) ≅ Z` and vanishing of
  `H¹` for the sheaf of germs of continuous real-valued functions.

II.1.21(d,e) is adopted only as supporting data for Exercise 2.2. Exercises
2.1, 2.5, and 2.6 have no running-text delegation or later-use citation in the
audited source and are not roadmap targets.

## Pinned Mathlib audit

The audited revision is `0df444a360eaa60ab8c11dca51a86af692955474`
(`v4.33.1`). Exact declarations are recorded on the relevant leaves. Focused
search found no exact full result for acyclic resolutions, universal delta
functors, enough injectives for `SheafOfModules`, injective-implies-flasque,
flasque acyclicity, filtered-colimit comparison, closed-pushforward
cohomology, cohomology with supports, or Grothendieck vanishing.
