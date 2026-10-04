# Hartshorne II.3, *First Properties of Schemes*

Robin Hartshorne, *Algebraic Geometry*, Chapter II, §3. Locators are printed
book pages. In the repository scan, `PDF index = printed page + 14` when the
first page has index zero.

## Source boundary

The section begins on printed p. 82 (PDF index 96), not p. 83, with the
definitions of connected, irreducible, reduced, and integral schemes and
Proposition 3.1. The running text ends on p. 90. The exercises begin there and
continue through p. 95 (index 109), where §4 starts. Thus the initially quoted
span pp. 83–94 omitted both the opening page and the last page of Exercise
3.20. This inventory uses the actual section boundary.

## Reduced, integral, and Noetherian schemes

- **Definitions and Proposition 3.1, p. 82.** Connectedness and irreducibility
  are properties of the underlying topological space. A scheme is reduced when
  every section ring is reduced, equivalently when every stalk is reduced. A
  scheme is integral when its section rings on nonempty opens are domains.
  Proposition 3.1 says that a scheme is integral exactly when it is reduced and
  irreducible. Example 3.0.1 gives the three affine criteria in terms of the
  nilradical and domain structure of the ring.
- **Definition and Proposition 3.2, pp. 83–84.** A scheme is locally Noetherian
  when it has an affine cover by spectra of Noetherian rings, and Noetherian
  when it is also quasi-compact. Proposition 3.2 proves that every affine open
  in a locally Noetherian scheme has a Noetherian section ring. Its algebraic
  core descends Noetherianity from finitely many principal localizations whose
  defining elements generate the unit ideal.

Hartshorne literally says that every open section ring of an integral scheme
is a domain. The empty open has the zero ring of sections, so the intended and
Mathlib-compatible statement is restricted to nonempty opens.

## Finite-type and finite morphisms

- **Definitions, p. 84.** Locally finite type is defined using affine covers of
  target inverse images by affines with finitely generated coordinate
  algebras. Finite type additionally requires finite such covers. A finite
  morphism has affine inverse images of affine opens and module-finite
  coordinate algebras.
- **Exercises 3.1–3.4, pp. 90–91.** These properties can be tested over every
  affine target open. Quasi-compact morphisms are likewise detected there.
  Finite type is equivalent to locally finite type plus quasi-compactness, and
  every affine source open over an affine target open then has finitely
  generated coordinate algebra.
- **Exercise 3.13, p. 93.** Closed immersions and quasi-compact open immersions
  are finite type; finite type is stable under composition and base extension;
  products over a base are finite type; finite type cancels from a composite
  when the first map is quasi-compact; a finite-type scheme over a Noetherian
  scheme is Noetherian.

Mathlib exposes `LocallyOfFiniteType f` and `QuasiCompact f` as the component
predicates. The project uses the transparent, non-typeclass source-facing
abbreviation `Hartshorne.FiniteType f := LocallyOfFiniteType f ∧ QuasiCompact f`.

## Subschemes and dimension

- **Definitions and Examples 3.2.3–3.2.6, pp. 85–86.** Open immersions identify
  their source with an open subscheme. Closed immersions are closed embeddings
  with surjective structure-sheaf map. Quotients `A → A/I` yield all closed
  subschemes of an affine scheme. For a closed set, the vanishing ideal sheaf
  gives the reduced induced closed subscheme.
- **Dimension and codimension, p. 86.** Scheme dimension is topological Krull
  dimension. The codimension of an irreducible closed subset is the supremum
  of chains beginning there; for an arbitrary closed subset it is the infimum
  over its irreducible closed subsets. Example 3.2.7 identifies affine-scheme
  dimension with ring Krull dimension.
- **Exercise 3.11(b)–(d), p. 92.** Affine closed subschemes come from ideals;
  the reduced induced structure is the smallest structure on its support; and
  every morphism has a smallest closed scheme-theoretic image. The reduced
  source clause identifies that image with the reduced induced structure on
  the closure of the set-theoretic image.

Mathlib represents closed subschemes as ideal sheaves or objects over the
ambient scheme, rather than literal equivalence classes of closed immersions.
It has the vanishing ideal sheaf and subscheme construction, but no verified
theorem that the resulting vanishing-ideal subscheme is reduced. It also lacks
Hartshorne's codimension of an arbitrary closed subset.

For scheme-theoretic images, current Mathlib already provides
`Scheme.Hom.image`, `imageι`, `toImage`, `toImage_imageι`, and the
kernel/subscheme adjunction. These directly support the existence and
universality leaf. The reduced-source identification is kept separate because
the available theorem identifying the support of the kernel with the closure
of the range assumes quasi-compactness, whereas Hartshorne's statement does
not.

## Fiber products, fibers, and base extension

- **Theorem 3.3, pp. 87–88.** Fiber products of schemes exist and are unique up
  to unique isomorphism. The proof constructs the affine case as
  `Spec (A ⊗[R] B)`, proves that compatible morphisms glue, restricts a
  product over an open in one factor, and glues local products.
- **Fibers and base extension, pp. 89–90.** The fiber over `y` is
  `X ×_Y Spec κ(y)`. Base extension is pullback along a new base and is
  transitive. Finite type is stable under base extension, whereas integral
  fibers need not remain irreducible or reduced.
- **Exercise 3.10(a), p. 92.** The fiber's underlying space is homeomorphic to
  the set-theoretic inverse image with its induced topology.

Mathlib's `CategoryTheory.Limits.pullbackIsPullback` exactly supplies the
fiber-product universal property and is recorded as `mathlib: true`. The
source-shaped existence theorem remains a separate local wrapper because the
`HasPullbacks Scheme` instance itself is anonymous.

## Later-used exercises

The project policy adopts an exercise only when later running text uses it.
Besides the exercises already invoked by §3 itself, the following qualify:

- **Exercise 3.6, p. 91:** the function field of an integral scheme. Used in
  the running text on II p. 112.
- **Exercise 3.7, p. 91:** a dominant generically finite finite-type morphism of
  integral schemes is finite over a dense open. Used on IV p. 314.
- **Exercise 3.8, p. 91:** normal schemes and normalization, including its
  universal property and finiteness over a field. Used repeatedly from II
  pp. 148 and 185 onward.
- **Exercise 3.11(d), p. 92:** scheme-theoretic images. Used in II §4 and later.
- **Exercise 3.12, p. 92:** closed subschemes of `Proj`. Used in II on
  pp. 103, 119–120, and 162.
- **Exercise 3.14, p. 93:** density of closed points for schemes finite type
  over a field. Used on II p. 104.
- **Exercise 3.16, p. 93:** Noetherian induction. Used explicitly in the
  running proof on III p. 214.
- **Exercise 3.17(e), pp. 93–94:** only the later-used specialization
  terminology and stability of closed/open sets are adopted. Used on II
  pp. 97–98.
- **Exercise 3.20(a),(c),(d),(f), pp. 94–95:** the closed-point local dimension,
  codimension as an infimum of local dimensions, the dimension/codimension
  formula, and preservation of component dimension under field extension.
  These are used together in later local-dimension arguments on III pp. 257
  and 269. The roadmap states parts (c) and (d) for nonempty closed subsets so
  that no arithmetic convention for the empty set is hidden in a theorem.

## Excluded exercises and examples

Exercises 3.5, 3.9, 3.10(b), 3.11(a), 3.15, the unused parts of 3.17,
3.18–3.19, 3.20(b),(e), and 3.21–3.23 are not adopted. Later references
found for several of them occur only inside other exercises. Exercise 3.11(a)
is already in Mathlib as stability of closed immersions under base change, but
no later running-text dependency was found.

Examples 3.2.1, 3.2.2, 3.2.4, 3.2.5, 3.3.1, and 3.3.2 are retained as examples
and prospective tests, not separate theorem nodes. The discussion of families,
deformations, reduction modulo `p`, Grothendieck's relative philosophy, the two
cautions, and Figure 7 is expository terminology rather than an additional
formalization target.

## Representation and upstream gaps

The pinned checkout already contains exact APIs for reduced and integral
schemes, Proposition 3.1, Proposition 3.2, finite and finite-type morphism
machinery, open and closed immersions, affine closed subschemes, pullbacks,
fibers, function fields, Jacobson density, and specialization.

For normalization, the closest prior art is
`Mathlib/AlgebraicGeometry/Normalization.lean`. Given a quasi-compact,
quasi-separated morphism `f : X → Y`, it constructs the relative normalization
`f.normalization`, the maps `f.toNormalization` and `f.fromNormalization`,
identifies affine sections with integral closures, proves reducedness and
integrality under corresponding hypotheses on the source, and supplies
`normalizationDesc` and `normalization.hom_ext` for its relative universal
property. This is valuable proof infrastructure but is not an exact statement
of Exercise 3.8: the pinned checkout has no scheme-level normality predicate,
does not package the absolute normalization obtained from the function field,
does not prove Hartshorne's normal-source universal property in that form, and
does not prove finiteness over a field. The normalization leaves are therefore
source-shaped wrappers around this prior art, not `mathlib: true` results.

Substantive gaps remain for: reducedness of the reduced induced subscheme;
arbitrary-closed-subset codimension; the generically-finite dense-open theorem;
a scheme-level normality predicate; Hartshorne's absolute normalization,
normality, universal property, and finiteness; closed immersions induced by
graded quotient maps on `Proj`; and the adopted parts of Exercise 3.20.
