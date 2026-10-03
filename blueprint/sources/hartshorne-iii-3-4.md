# Hartshorne III.3–4, *Affine and Čech Cohomology*

Robin Hartshorne, *Algebraic Geometry*, Chapter III, §§3–4, printed
pp.213–225. In the repository PDF these are one-based PDF pages 228–240
(zero-based indices 227–239); the one-based PDF page number is the printed
page number plus 15.

## Source boundary and adoption policy

The adopted running text begins with Proposition 3.1A on printed p.213 and
ends with Theorem 4.5 on p.222. The exercise boundary continues through
printed p.225 so that the adopted chains 3.1–3.4, 4.1–4.2, 4.4–4.6, 4.8,
4.10, and 4.11 are complete. Exercise 4.8(e) is not adopted under the
clause-level policy: its set-theoretic-complete-intersection application is
not used by the selected later chain. Exercise 4.9 is also not adopted: its
set-theoretic-complete-intersection chain would also require Exercises 2.3,
2.4, and 4.3 and is not a prerequisite of the selected running results.
Exercises 3.5–3.8 and 4.7 are deferred.

Hartshorne assumes Noetherian hypotheses throughout these sections. The
roadmap preserves them even where later literature or Mathlib primitives are
more general.

## Affine cohomology

- **Proposition 3.1A (Krull/Artin–Rees), p.213.** For finite modules
  `M ⊆ N` over a Noetherian ring and an ideal `a`, the `a`-adic topology on
  `M` is induced from that on `N`: for every `n` there is `n' ≥ n` with
  `a^n M ⊇ M ∩ a^n' N`. Hartshorne cites Atiyah–Macdonald, Theorem 10.11,
  and Zariski–Samuel, volume II, Chapter VIII, Theorem 4.
- **Lemma 3.2, pp.213–214.** If `I` is injective, its submodule
  `Γ_a(I) = {x | a^n x = 0 for some n}` is injective. The proof uses 3.1A
  and Baer's criterion.
- **Lemma 3.3, p.214.** For `f ∈ A`, the canonical map `I → I_f` is
  surjective when `I` is injective and `A` is Noetherian.
- **Proposition 3.4, pp.214–215.** The sheaf `Itilde` on `Spec A` is flasque.
  Hartshorne uses Noetherian induction, Lemmas 3.2–3.3, and the identification
  of sections supported on `V(f)` with `Γ_(f)(I)`.
- **Theorem 3.5, p.215.** Positive cohomology of a quasi-coherent module on a
  Noetherian affine scheme vanishes. An injective resolution of the module is
  sent by tilde to a flasque resolution.
- **Corollary 3.6, p.215.** Every quasi-coherent module on a Noetherian scheme
  embeds in a flasque quasi-coherent module. The construction uses a finite
  affine cover and direct images of the affine flasque envelopes.
- **Theorem 3.7 (Serre), pp.215–216.** A Noetherian scheme is affine iff all
  positive quasi-coherent cohomology vanishes, equivalently iff `H^1(X,J)=0`
  for every coherent ideal sheaf. The difficult implication uses the finite
  principal-open affine criterion from II, Exercise 2.17.

## Local-cohomology exercises

- **Exercise 3.3(a), p.217.** For a Noetherian ring `A` and ideal `a`, the
  ideal-power torsion functor `Γ_a` is left exact; define its right derived
  functors `H_a^i`.
- **Exercise 3.3(b,c), p.217.** For `X = Spec A`, `Y = V(a)`, and an
  `A`-module `M`, compare algebraic local cohomology with sheaf cohomology
  with supports: `H_a^i(M) ≅ H_Y^i(X,Mtilde)`. Each resulting module is
  again `a`-power torsion.
- **Exercise 3.4, p.217.** For finite `M`, `depth_a M ≥ n` iff
  `H_a^i(M)=0` for every `i<n`. Part (a) identifies positive depth with
  vanishing of `Γ_a(M)` by associated primes; part (b) proceeds along a
  regular sequence. Hartshorne refers to Grothendieck [7] for details.

The roadmap adopts these exercises because they establish the algebraic and
supported-sheaf meanings of local cohomology before later duality arguments.
It does not define scheme cohomology internally in the quasi-coherent
subcategory: that alternative would require the separate comparison in
Exercise 3.6(c), which is outside the adopted chain.

## Cech construction and comparison

- **Definition and Remark 4.0.1, pp.218–219.** For a well-ordered open cover,
  Hartshorne forms the normalized alternating complex over strictly increasing
  tuples. Repeated-index components are declared zero and arbitrary tuples
  acquire the sign of the sorting permutation.
- **Caution 4.0.2, p.219.** For a fixed cover, Čech cohomology does not in
  general form a delta functor: taking sections on the intersections need not
  preserve a short exact sequence. Later long exact sequences therefore use
  acyclicity hypotheses or pass to refinement, rather than being built into
  fixed-cover Čech cohomology.
- **Lemma 4.1, p.220.** Degree-zero Čech cohomology is global sections.
- **Lemma 4.2, pp.220–221.** The sheafified Čech complex, whose terms are
  products of direct images from intersections, is a resolution. On a stalk,
  insertion of any cover member containing the point gives a contracting
  homotopy.
- **Proposition 4.3, p.221.** A flasque sheaf has no positive Čech
  cohomology.
- **Lemma 4.4, p.221.** Comparison with an injective resolution gives natural
  maps from Čech to derived-functor cohomology. Hartshorne cites
  Hilton–Stammbach, Chapter IV, §4.4, for the comparison-of-resolutions step.
- **Theorem 4.5, p.222.** On a Noetherian separated scheme, an affine open
  cover computes the cohomology of a quasi-coherent module. Separatedness is
  used exactly to make every finite intersection affine.
- **Exercise 4.11, p.225.** More generally, a cover computes cohomology when
  every finite intersection is acyclic for the sheaf. This is the Leray
  acyclic-cover theorem; Theorem 4.5 is its affine quasi-coherent corollary.

## Adopted exercises and later use

- **Exercises 3.1–3.2, p.216.** Affineness is invariant under reduction, and
  a reduced Noetherian scheme is affine iff all irreducible components are
  affine. They are used with Chevalley's theorem in III, Exercise 5.7 and IV,
  Exercise 1.4.
- **Exercise 4.1, p.222.** For an affine morphism,
  `H^i(X,F) ≅ H^i(Y,f_*F)`. It is reused in III, Exercise 5.7, Exercise 6.10,
  and §8, and in IV, Exercise 1.8.
- **Exercise 4.2, pp.222–223.** Chevalley's theorem says that a finite
  surjective image of an affine Noetherian separated scheme is affine. Its
  two generic coherent-approximation steps are retained as separate roadmap
  units before the final Noetherian-induction theorem.
- **Exercise 4.4, p.223.** The filtered colimit of first Čech cohomology over
  refinements is ordinary `H^1`.
- **Exercise 4.5, p.224.** `Pic X ≅ H^1(X,O_X^*)` for any ringed space. This
  is reused in III §7, IV §4, and Appendix B §5.
- **Exercise 4.6, p.224.** A square-zero ideal gives
  `0 → J → O_X^* → O_X0^* → 0` and the associated Picard exact sequence.
  It is reused in III, Exercises 5.8, 5.9, and 11.5 and IV §4.
- **Exercise 4.8(a–d), p.224.** Define cohomological dimension, reduce its
  testing to coherent and then locally free sheaves, bound it by the size of
  an affine cover, and construct a `dim X + 1` affine cover for
  quasi-projective schemes. Part (a) explicitly uses II, Exercise 5.15(e): on
  a Noetherian scheme every quasi-coherent module is the filtered union of
  its coherent subsheaves. That dual-source supporting result is adopted as
  its own roadmap leaf. Clause (e) is outside the adopted chain.
- **Exercise 4.10, p.225.** For a nonsingular variety and a coherent module
  `F`, infinitesimal extensions by `F` are classified by
  `H^1(X,F tensor T_X)`. Hartshorne refers to II, Exercise 8.7 for
  infinitesimal extensions and to II, Exercise 8.6 for the affine lifting
  input. The roadmap records
  this as a precise source-obligation node rather than silently treating the
  classification as proved by the sketch.

## Project-authored representation choices

1. Classical sheaf cohomology is the right-derived functor of global
   sections in sheaves of abelian groups. For an `O_X`-module, its cohomology
   is that of the underlying abelian sheaf. Mathlib's site-theoretic
   `Sheaf.H`, defined as Ext from a constant integer sheaf, may be used only
   after a proved comparison with this derived-global-sections definition.
2. The category of quasi-coherent modules is not used as the defining
   derived category. Any future QCoh-internal representation requires the
   explicit comparison of Exercise 3.6(c).
3. Algebraic local cohomology is first defined as the right derived functor
   of ideal-power torsion. Mathlib's Ext-colimit construction is admitted
   only after a natural comparison is proved.
4. The project uses Hartshorne's normalized ordered Čech complex. Mathlib's
   all-tuples Čech nerve is a partial primitive; a normalization
   quasi-isomorphism is required before transferring results between them.
5. The comparison in Exercise 3.3(b) is a theorem node, not definitional
   equality. The closed subset `V(a)`, tilde, and the two derived functors
   remain visible in its statement.
6. Cohomological dimension is extended project-authoredly from Hartshorne's
   least natural-number bound to a value in `WithTop Nat`; it is the infimum
   of all finite bounds, and is `top` when no finite bound exists.
7. Refinement Čech cohomology is not silently indexed by a poset. The roadmap
   requires an explicit small refinement category (or a proved equivalent
   small cofinal model), including the comparison of parallel refinement
   functions, before forming its colimit.

## Pinned Mathlib audit

The pinned checkout is Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`).

Exact supporting primitives include:

- `Ideal.exists_pow_inf_eq_pow_smul` in
  `Mathlib/RingTheory/Filtration.lean`;
- `Module.Injective`, `Module.Baer`, and `Module.Baer.iff_injective` in
  `Mathlib/Algebra/Module/Injective.lean`;
- `Submodule.primaryComponent` and `Submodule.primaryComponent_mem` in
  `Mathlib/Algebra/Module/Torsion/PrimaryComponent.lean`;
- `TopCat.Presheaf.IsFlasque`, `TopCat.Sheaf.IsFlasque`, flasque
  pushforward, and the short-exact closure lemmas in
  `Mathlib/Topology/Sheaves/Flasque.lean`;
- `CategoryTheory.Sheaf.H`, `H'`, `H.map`, and `functorH` in
  `Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`;
- `AlgebraicGeometry.tildeEquiv` and the affine tilde/global-sections
  comparison in `Mathlib/AlgebraicGeometry/Modules/Tilde.lean`;
- `AlgebraicGeometry.IsAffineOpen.inf` in
  `Mathlib/AlgebraicGeometry/Morphisms/Affine.lean`.

Partial, non-leaf-complete primitives include:

- `CategoryTheory.cechComplexFunctor` in
  `Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean`, which does not
  supply Hartshorne's normalization or comparison theorem;
- the Ext-colimit model in `Mathlib/Algebra/Homology/LocalCohomology.lean`,
  whose file explicitly leaves comparison with derived torsion and Čech
  models as future work;
- general right-derived-functor and injective-resolution infrastructure,
  which does not itself prove affine vanishing, flasque acyclicity, or the
  classical/site cohomology comparison.

No complete pinned declaration was found for Lemmas 3.2–3.4, Theorems
3.5 or 3.7, the supported/local-cohomology comparison, depth detection, the
Čech comparison theorems, Picard-as-`H^1`, or Chevalley's theorem.

## External proof obligations

- Proposition 3.1A is grounded in the two references cited by Hartshorne and
  the exact stronger pinned Artin–Rees declaration.
- The derived-torsion/local-cohomology comparison and the depth theorem need
  a cited treatment such as Grothendieck [7] or an appropriate Stacks
  Project local-cohomology section; Hartshorne's exercise text is only a
  proof outline.
- Lemma 4.4 uses Hilton–Stammbach IV.4.4. Exercise 4.11 needs a complete
  double-complex or acyclic-resolution proof, including convergence and
  exactness of the products involved, not merely the exercise instruction.
- Exercise 4.4 additionally requires a small refinement-category model and a
  proof that parallel refinement functions induce the same map after further
  refinement.
- Exercise 4.8(d) needs a scheme-level source for the construction of a
  `dim X + 1` affine cover of an arbitrary quasi-projective scheme; a
  variety-only hyperplane argument is not accepted as a substitute.
- Exercises 4.2, 4.4–4.6, 4.8(a–d), and 4.10 are source sketches. Their roadmap
  statements are fixed here, but detailed proofs must either cite a secondary
  source or be explicitly labeled project-authored.
- Exercise 4.10 remains `not_ready` until II, Exercise 8.6's precise category
  of square-zero extensions, equivalence relation, and tensor convention are
  reconciled with the deformation cocycle statement.
