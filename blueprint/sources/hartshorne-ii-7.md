# Hartshorne II.7, *Projective Morphisms*

Robin Hartshorne, *Algebraic Geometry*, Chapter II, §7. Locators below are
printed book pages. In the repository scan, zero-based `PDF index = printed
page + 14`.

## Source boundary

The section begins at the foot of printed p.149. Its running mathematics is on
pp.150–169. The requested exercise span ended on p.171, but Exercise 7.14(a)
is cited by Caution 7.8.8 and its companion clause 7.14(b) ends at the top of
p.172. This inventory therefore stops at that point, before §8 begins.

The roadmap adopts the running definitions and assertions. It adopts Exercise
7.1 because Proposition 7.14 uses it; Exercises 7.8–7.10 because the note after
Proposition 7.12 delegates projective-bundle properties to them; Exercise
7.11(a,b) because Remark 7.17.1 cites the nonuniqueness they exhibit; and
Exercise 7.14 because Caution 7.8.8 cites it. Independent review also adopts
Exercise 7.5(d), both elementary clauses of Exercise 7.6 while recording its
later Riemann–Roch conclusion as blocked, and Exercise 7.7(c). Exercises
7.2–7.4, the other clauses of 7.5, 7.7(a,b), Exercise 7.11(c), and Exercises
7.12–7.13 are not roadmap targets.

## Morphisms, ampleness, and linear systems

- **Theorem 7.1, pp.150–151.** Morphisms to projective space correspond to an
  invertible sheaf together with finitely many global generators. The inverse
  image of a standard affine chart is the nonvanishing locus of the
  corresponding section.
- **Propositions 7.2–7.3 and Lemma 7.4, pp.151–153.** Closed immersions are
  characterized first chartwise and then, over an algebraically closed field,
  by separation of closed points and tangent vectors. The proof uses the local
  algebra lemma that a finite local map with the same residue field and a
  surjection on cotangent spaces is surjective.
- **Ample definition, Proposition 7.5, and Theorem 7.6, pp.153–156.** An
  invertible sheaf is ample when every coherent sheaf becomes globally
  generated after all sufficiently large twists. Positive tensor powers do not
  change ampleness. On a finite-type scheme over a Noetherian ring, ampleness
  is equivalent to some positive power being very ample.
- **Proposition 7.7, definitions, and Lemma 7.8, pp.156–159.** Nonzero sections
  of `O(D)` modulo scalars correspond to effective divisors linearly equivalent
  to `D`. Define complete linear systems, linear subsystems, base points, and
  traces. Base-point-freeness is equivalent to generation by the chosen
  sections. Remarks 7.8.1–7.8.2 translate Theorem 7.1 and Proposition 7.3 into
  linear-system language.

Examples 7.1.1–7.1.2, 7.4.2, 7.6.1–7.6.4, and 7.8.3–7.8.6 are retained as
examples and tests rather than separate theorem targets.

## Relative Proj and projective bundles

- **Relative Proj construction, pp.160–161.** For a quasi-coherent graded
  algebra generated coherently in degree one, glue affine Proj schemes and
  their `O(1)` sheaves.
- **Lemma 7.9, p.161.** Tensoring degree `d` by `L^d` does not change relative
  Proj, while it changes `O(1)` by tensoring with the pullback of `L`.
- **Proposition 7.10, pp.161–162.** Relative Proj is proper. If the base has an
  ample invertible sheaf, a suitable twist of `O(1)` is relatively very ample,
  so the projection is projective.
- **Definition and Propositions 7.11–7.12, pp.162–163.** On a Noetherian base,
  define `P(E)=Proj Sym(E)` for finite locally free `E`. For rank at least two,
  its twists recover the symmetric algebra under pushforward. It has the
  tautological quotient `pi^* E -> O(1)` and represents invertible quotients
  of pullbacks of `E`, modulo isomorphism of the quotient line bundle.

The convention is the quotient convention. A point of `P(E)` is an invertible
quotient of `E`, and the tautological map is `pi^* E -> O(1)`. Replacing `E`
by its dual silently reverses Proposition 7.11, Proposition 7.12, and the
twisting formula, so the roadmap must not do so.

## Blowups

- **Definition, pp.163–164.** For a coherent ideal `I`, define the blowup by
  `Proj_X (direct-sum_d I^d)`. Hartshorne separately defines the inverse-image
  ideal as the image of `f^* I -> O_X`; it need not equal the module pullback
  `f^* I`.
- **Propositions 7.13–7.14, pp.164–165.** On the blowup the inverse-image ideal
  is invertible and identifies with `O(1)` in Hartshorne's grading convention;
  the blowup is an isomorphism off the center and is universal among maps on
  which the inverse-image ideal is invertible.
- **Corollary 7.15 and Example 7.15.1, pp.165–166.** Blowups are functorial for
  pulled-back centers, preserve closed immersions in this construction, and
  define strict transforms. In the exact comparison made by the source, for
  an integral closed subvariety `Y` of affine space through the origin with
  `Y` not equal to that point, the strict transform is the closure of the
  inverse image of the punctured `Y` and agrees with the Chapter-I affine
  construction.
- **Proposition 7.16, p.166.** A nonzero blowup of a variety is a variety and
  is birational, proper, and surjective; quasi-projectivity and projectivity
  are preserved.
- **Theorem 7.17, pp.166–168.** Every projective birational morphism to a
  quasi-projective variety is a blowup of a coherent ideal. Step 2's eventual
  degree-one generation after a Veronese replacement is covered by the
  existing eventual section-recovery and Veronese-Proj roadmap nodes.
- **Example 7.17.3, pp.168–169.** Blowing up the base ideal of finitely many
  sections eliminates the associated rational map's indeterminacy.

The sign convention is fixed by Proposition 7.13: with the Rees algebra
`direct-sum I^d` used here, the invertible inverse-image ideal is `O(1)`. If
`E` is its effective exceptional Cartier divisor, then
`I_E ≅ O(1) ≅ O(-E)`.

## Adopted exercises

- **7.1, p.169:** a surjective morphism of invertible sheaves is an isomorphism.
- **7.5(d), p.169:** a very ample sheaf tensored with a globally generated
  invertible sheaf is very ample.
- **7.6, p.170:** for very ample `D`, `dim |nD|` is eventually the Hilbert
  polynomial minus one; for torsion `D`, it is periodic. Eventual
  polynomiality for arbitrary ample `D` depends on the later Riemann–Roch
  theorem and is kept as a separate blocked obligation.
- **7.7(c), p.170:** blowing up the base point of the conics through a point of
  `P^2` resolves the subsystem to a closed immersion as a cubic ruled surface
  in `P^4`.
- **7.8–7.10, pp.170–171:** sections and invertible quotients of `E`, the Picard
  group and twist classification of `P(E)`, and projective-space bundles. For
  disconnected `X`, the corrected Picard formula uses locally constant
  integer-valued functions in place of one global integer. The Picard formula
  and the classification of regular projective-space bundles remain blocked
  pending proof-level sources.
- **7.11(a,b), p.171:** invariance of blowup under powers and invertible ideal
  factors. The stronger minimal-support assertion in 7.11(c) is not adopted.
- **7.14, pp.171–172:** for the chosen counterexample `X = P^1` and
  `E = O_X(-1)`, the quotient convention gives `P(E) ≅ X` and tautological
  `O(1) ≅ E`, which is not relatively very ample because it is not globally
  generated. An ample twist becomes very ample over a composite base.

## Pinned Mathlib audit

The pinned checkout is Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
Useful exact primitives are:

- `AlgebraicGeometry.Proj.fromOfGlobalSections` and its standard-open formulas
  in `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean`;
- `AlgebraicGeometry.Proj.map` and its functoriality in
  `ProjectiveSpectrum/Functor.lean`;
- the properness instance for `Proj.toSpecZero` in
  `ProjectiveSpectrum/Proper.lean`;
- `Scheme.IdealSheafData`, its products and powers, and
  `Scheme.IdealSheafData.comap` in `IdealSheaf/Basic.lean` and
  `IdealSheaf/Functorial.lean`;
- `reesAlgebra` and `adjoin_monomial_eq_reesAlgebra` in
  `Mathlib/RingTheory/ReesAlgebra.lean`;
- `SymmetricAlgebra.ι`, `SymmetricAlgebra.lift`, and
  `SymmetricAlgebra.equivMvPolynomial` in
  `Mathlib/LinearAlgebra/SymmetricAlgebra/`;
- `SheafOfModules.IsLocallyFree` and the free-sheaf section API in
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/`.

These are affine or algebraic infrastructure, not exact formalizations of the
relative-Proj, ampleness, projective-bundle, or blowup assertions below. No
roadmap leaf is marked `mathlib: true` from these partial matches.

## Adopted auxiliary proof sources

Hartshorne is the statement source. The following Stacks Project sections are
adopted for details Hartshorne omits:

- morphisms into Proj: §§27.12 and 27.14, tags `01N4`, `01NJ`;
- relative Proj: §§27.15–27.16, tags `01NM`, `01NS`;
- projective bundles: §27.21, tag `01OA`;
- ample invertible sheaves: §28.27, tag `01PR`;
- projective morphisms: §29.44, tag `01W7`;
- blowups and their universal property: §31.33, tags `01OF`, `0806`.

Still unresolved are complete proof sources for Exercises 7.9–7.10 and the
precise later Riemann–Roch theorem supporting the ample conclusion of Exercise
7.6. Exercise 7.14(a) is fixed to the `P^1`, `O(-1)` example above.
