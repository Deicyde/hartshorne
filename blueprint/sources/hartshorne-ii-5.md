# Hartshorne II.5, *Sheaves of Modules*

Robin Hartshorne, *Algebraic Geometry*, Chapter II, §5. Locators are printed
book pages. In the repository scan, zero-based `PDF index = printed page + 14`.

## Source boundary

The editorial introduction occurs at the foot of printed p.108. The adopted
mathematics begins on p.109 and the running text ends with Corollary 5.20 on
p.123. The exercises begin on p.123. Exercise 5.18 starts on p.128 and ends on
p.129; it is completed here because later running text explicitly delegates to
the exercise. Section II.6 begins immediately afterwards on p.129.

The roadmap uses Hartshorne's running definitions and assertions as the
mathematical specification. Mathlib's local-presentation definition of
quasi-coherence is the implementation representation. On locally Noetherian
schemes, the roadmap first proves that Mathlib finite presentation agrees with
Hartshorne's affine-local finite-generation definition of coherence.

## Modules, quasi-coherence, and exactness

- **Definitions, pp.109–110.** Sheaves of `O_X`-modules; morphisms, kernels,
  cokernels, images, quotients, limits and colimits; sheaf Hom, tensor product,
  free, locally free and invertible modules; ideal sheaves; module direct and
  inverse image; and the adjunction `f^* ⊣ f_*`.
- **Propositions 5.1–5.2, pp.110–111.** For an `A`-module `M`, the associated
  sheaf `M~` has stalk `M_p`, sections `M_f` on `D(f)`, and global sections
  `M`. The tilde functor is exact and fully faithful, preserves tensor products
  and sums, and identifies affine pullback and pushforward with extension and
  restriction of scalars.
- **Definition and Examples 5.2.1–5.2.5, pp.111–112.** Quasi-coherent and
  coherent modules, with the structure sheaf, closed-subscheme structure
  sheaves, extension by zero, quotient sheaves on the wrong space, and the
  constant function-field sheaf as examples or warnings.
- **Lemma 5.3, p.112.** A section vanishing on `D(f)` is killed by a power of
  `f`; a section over `D(f)` extends after multiplication by a power of `f`.
- **Proposition 5.4 and Corollary 5.5, p.113.** The affine-local criterion and
  the equivalence between `A`-modules and quasi-coherent modules on `Spec A`,
  including finite modules/coherent sheaves in the Noetherian case.
- **Propositions 5.6–5.8, pp.113–115.** Affine global sections are exact when
  the kernel is quasi-coherent; quasi-coherent and Noetherian coherent modules
  are closed under kernels, cokernels, images, and extensions; pullback
  preserves quasi-coherence and Noetherian coherence; and pushforward
  preserves quasi-coherence under the stated Noetherian or quasi-compact
  separated hypotheses.

These results are represented in the sibling
`modules-and-quasicoherent` roadmap chapter and are prerequisites below.

## Ideal sheaves and closed subschemes

- **Definition and Proposition 5.9, pp.115–116.** The ideal sheaf of a closed
  immersion is the kernel of `O_X → i_* O_Y`. It is quasi-coherent, coherent
  when `X` is Noetherian, and every quasi-coherent ideal sheaf determines a
  unique closed subscheme.
- **Corollary 5.10, p.116.** Ideals of `A` correspond to closed subschemes of
  `Spec A`; every closed subscheme of an affine scheme is affine.

Mathlib's `Scheme.IdealSheafData` stores compatible ideals on affine opens and
is explicitly not yet an actual `O_X`-submodule. The roadmap therefore keeps
the module ideal sheaf and `IdealSheafData` distinct, proves a bridge, and only
then reuses `IsClosedImmersion.overEquivIdealSheafData`.

## Graded modules, twists, and reconstruction on Proj

- **Definition and Proposition 5.11, pp.116–117.** A graded `S`-module `M`
  determines an `O_Proj S`-module `M~`; its stalks and standard-chart sections
  are degree-zero homogeneous localizations. It is quasi-coherent, and is
  coherent when `S` is Noetherian and `M` is finite.
- **Definition and Proposition 5.12, p.117.** Define `O_X(n)=S(n)~` and
  `F(n)=F tensor O_X(n)`. If `S` is generated in degree one, the twists are
  invertible, twisting commutes with graded-module shifts and tensor products,
  and graded-ring maps pull twists back compatibly. For the induced
  `f : U → Proj S` from an open of `Proj T`, the source also identifies
  `f_*(O_{Proj T}(n)|_U)` with `(f_*O_U)(n)`.
- **Definition and Proposition 5.13, p.118.** Define
  `Gamma_*(F)= direct-sum_n Gamma(X,F(n))`. For projective space over `A`,
  `Gamma_*(O_X)` is the polynomial ring `A[x_0,...,x_r]` when `r >= 1`.
- **Lemma 5.14, pp.118–119.** For a section of an invertible sheaf, vanishing
  and extension across its nonvanishing locus hold after multiplication by a
  sufficiently high tensor power.
- **Proposition 5.15, p.119.** If `S` is finitely generated in degree one and
  `F` is quasi-coherent on `Proj S`, the natural map `Gamma_*(F)~ → F` is an
  isomorphism.
- **Corollary 5.16, pp.119–120.** Every closed subscheme of projective space is
  defined by a homogeneous ideal, and projective schemes over `Spec A` are
  exactly `Proj S` for suitable degree-one-generated graded `A`-algebras.

## Very ample sheaves and projective finiteness

- **Definitions and Remark 5.16.1, p.120.** Define relative `O(1)` and relative
  very ampleness. Over a Noetherian base, projective is equivalent to proper
  together with a relatively very ample invertible sheaf.
- **Definition and Examples 5.16.2–5.16.3, p.121.** A module sheaf is generated
  by global sections exactly when it is a quotient of a free sheaf. Affine
  quasi-coherent sheaves and `O(1)` on degree-one-generated Proj are examples.
- **Theorem 5.17 and Corollary 5.18, pp.121–122.** A sufficiently positive
  twist of a coherent sheaf on a projective scheme over a Noetherian ring is
  finitely globally generated. Consequently every such coherent sheaf is a
  quotient of a finite direct sum of twists.
- **Theorem 5.19, pp.122–123.** If `A` is a finite-type algebra over a field,
  `X` is projective over `A`, and `F` is coherent, then `Gamma(X,F)` is a finite
  `A`-module. Hartshorne's proof uses a graded prime filtration and the
  finiteness of integral closure from Theorem I.3.9A.
- **Corollary 5.20, p.123.** A projective morphism between finite-type schemes
  over a field pushes coherent sheaves forward to coherent sheaves.

## Adopted exercises and later-use evidence

- **Exercise 5.1(a–d), pp.123–124.** Finite locally free duality, tensor-Hom,
  and the projection formula. Used in II p.143, III §6, and V p.380.
- **Exercise 5.3, p.124.** The affine tilde/global-sections adjunction. Used in
  Proposition 5.4 and Exercise 5.15.
- **Exercise 5.5(a–c), p.124.** The coherence counterexample, closed
  immersions are finite, and finite pushforward preserves coherence. Used in
  Caution 5.8.1, Theorem 5.17, and Chapter III.
- **Exercise 5.6(d,e), p.124.** Sections with support are affine power torsion,
  and sections with support preserve quasi-coherence and coherence. Parts
  (a)–(c) are retained only as internal support lemmas. The construction is
  used throughout III pp.213–215.
- **Exercise 5.7(a,b), pp.124–125.** Freeness of a coherent stalk extends to a
  neighbourhood, and local freeness is stalkwise. Used on II p.178.
- **Exercise 5.9(a,b), p.125.** The natural graded map to `Gamma_*` and its
  eventual isomorphism. Used in Theorem 5.19 and on II p.167.
- **Exercise 5.10(a–c), p.125.** Saturation and the largest homogeneous
  ideal defining a projective closed subscheme. Corollary 5.16 delegates this
  refinement to the exercise.
- **Exercise 5.12(a,b), p.126.** Tensoring very ample sheaves and composing
  relative very ample data. Used later in projective geometry.
- **Exercise 5.13, p.126.** Veronese Proj and the identification of its `O(1)`
  with `O(d)`. Used on II pp.155 and 167.
- **Exercise 5.14(a–d), p.126.** Section rings, integral closure,
  projectively normal Veronese embeddings, and the section-surjectivity
  criterion. Used by Remark 5.13.1 and later in Chapters II and III.
- **Exercise 5.15(a–d), pp.126–127.** Extension of coherent sheaves from an
  open subset of a Noetherian scheme. Used on II p.154 and in Chapter III.
- **Exercise 5.16, definitions and parts (b),(d), pp.127–128.** Tensor,
  symmetric, and exterior operations; the perfect exterior pairing; and the
  exterior-power filtration of a short exact sequence. Used in II–III.
- **Exercise 5.17(a–d), p.128.** Affine morphisms, relative Spec of a
  quasi-coherent algebra, and its classification. Relative Spec is used in the
  running text on III p.280.
- **Exercise 5.18(a–d), pp.128–129.** Geometric vector bundles and their
  correspondence with finite locally free sheaves. Explicitly referenced on
  II p.163. Hartshorne uses the convention `V(E)=Spec Sym(E)`, so its sheaf of
  sections is `E dual`; replacing `E` by `E dual` silently reverses the
  convention.

## Excluded exercise clauses

Exercises 5.2, 5.8, and 5.11 are not adopted. Exercise 5.4 is recorded as the
representation bridge but is not a separate exercise node. Parts 5.7(c),
5.9(c), 5.10(d), 5.15(e), 5.16(a),(c),(e), and 5.17(e) are not independent
targets under the running-text dependency policy. Examples 5.2.1–5.2.5 and
5.16.2–5.16.3 are examples or tests, not theorem nodes.

## Pinned Mathlib overlap and gaps

The pinned revision is `0df444a360eaa60ab8c11dca51a86af692955474`
(`v4.33.1`). Exact reusable declarations include:

- `Scheme.Modules`, its abelian structure, `pushforward`, `pullback`, and
  `pullbackPushforwardAdjunction` in
  `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`;
- `tilde`, `tilde.adjunction`, `tildeEquiv`, and affine localization formulas
  in `Mathlib/AlgebraicGeometry/Modules/Tilde.lean`;
- `SheafOfModules.IsQuasicoherent`, `IsFiniteType`, and
  `IsFinitePresentation` in the ModuleCat sheaf files;
- `IsClosedImmersion.overEquivIdealSheafData` in
  `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`;
- `Module.support`, `Module.support_of_exact`, and
  `Module.support_eq_zeroLocus` in `Mathlib/RingTheory/Support.lean`;
- `Module.freeLocus` and `Module.isOpen_freeLocus` in
  `Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean`;
- `Proj.basicOpenIsoSpec`, `Proj.basicOpenIsoAway`, `Proj.stalkIso`, and
  `Proj.toSpecZero` in the projective-spectrum files.

There is no graded-module sheafification on Proj, twisting-sheaf or
`Gamma_*` API, module-sheaf support or sections-with-support API, relative
Spec of a quasi-coherent algebra, geometric vector-bundle correspondence, or
sheaf-module tensor/internal-Hom/symmetric/exterior package. These are project
targets, not upstream claims.

Remark 5.19.2 observes that Theorem 5.19 only needs the base ring to be
Nagata. The present fine roadmap retains Hartshorne's stated finite-type
algebra hypothesis. The extension to arbitrary Nagata base rings is explicitly
deferred and is not claimed by the general-field finite-integral-closure
prerequisite used here.
