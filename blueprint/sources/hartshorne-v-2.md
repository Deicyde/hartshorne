# Hartshorne V.2, ruled surfaces

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter V, §2, printed pp.369–385. The final Exercise 2.17 begins on p.385
and concludes at the top of p.386, immediately before §3; it is included in
the exercise inventory below.

Chapter V's standing convention remains in force: the base field is
algebraically closed, surfaces are nonsingular and projective, and curves on
surfaces are effective divisors.

## Ruled surfaces and projective bundles, printed pp.369–371

A geometrically ruled surface is a surface `pi:X -> C` over a nonsingular
curve, all of whose fibres are `P^1`, together with a section. Hartshorne
notes that Tsen's theorem makes the section redundant, but the adopted
definition includes it. Products `C times P^1` are the basic examples, and
every ruled surface is birational to such a product.

Lemma 2.1 says that if `D.f=n>=0`, then `pi_*O_X(D)` is locally free of rank
`n+1`; in particular `pi_*O_X=O_C`. The proof combines constancy of fibre
degree, the cohomology of `P^1`, and Grauert.

Proposition 2.2 presents every ruled surface as the quotient-convention
projective bundle `P_C(E)` of a rank-two locally free sheaf. Conversely every
such projectivization is ruled. Moreover

`P(E) ~= P(E')` over `C` exactly when `E' ~= E tensor L`

for an invertible sheaf `L` on `C`.

For a section `C_0` and a fibre `f`, Proposition 2.3 gives

`Pic X ~= Z*[C_0] direct-sum pi^*Pic C`,

and `Num X ~= Z^2`, with `C_0.f=1` and `f^2=0`. Lemma 2.4 gives vanishing of
the positive higher direct images of `O_X(D)` when `D.f>=0`, together with
the corresponding Leray cohomology comparison. Corollary 2.5 computes

`p_a(X)=-g(C)`, `p_g(X)=0`, and `q(X)=g(C)`.

## Sections and normalization, printed pp.371–373

Proposition 2.6 identifies sections of `P(E)` with invertible quotients
`E -> L`. It also identifies the kernel line bundle from the divisor of the
section. Corollary 2.7 concludes that every rank-two bundle on a curve is an
extension of two invertible sheaves; Remark 2.7.1 delegates the arbitrary-
rank filtration to Exercise 2.3(a).

Proposition 2.8 twists `E` to a normalized representative characterized by

`H^0(C,E) != 0`, and `H^0(C,E tensor L)=0` whenever `deg L<0`.

The integer `e=-deg E` is then an invariant of the ruled surface, even when
the normalized bundle itself is not unique. A nonzero section of `E` gives a
distinguished section `C_0` with `O_X(C_0)=O_X(1)`.

With `det E=O_C(epsilon)`, write pullbacks of base divisors as multiples of
`f`. Proposition 2.9 says that a section corresponding to
`E -> O_C(b)` satisfies

`deg b=C_0.D`, `D~C_0+(b-epsilon)f`, and `C_0^2=deg epsilon=-e`.

## Canonical class and standard examples, printed pp.373–375

Lemma 2.10 and Corollary 2.11 give

`K_X ~ -2*C_0+(kappa+epsilon)f`,

where `kappa` is canonical on the base, and numerically

`K_X == -2*C_0+(2g-2-e)f`, `K_X^2=8*(1-g)`.

Examples 2.11.1–3 describe normalized decomposable bundles. Example 2.11.4
identifies the blowup of the vertex of a cone over an embedded smooth curve
`C` with `P_C(O_C direct-sum O_C(-1))`; its exceptional section has square
minus the degree of `C`. The blowup of `P^2` at a point is the invariant-one
rational ruled surface. Example 2.11.6 constructs the normalized
indecomposable elliptic example of invariant `-1` as a nonzero extension.

## Bounds and classification, printed pp.376–379

Theorem 2.12 classifies normalized decomposable bundles as
`O_C direct-sum L` with `deg L<=0`, so every `e>=0` occurs. For an
indecomposable normalized rank-two bundle it proves

`-2g <= e <= 2g-2`.

Consequently the rational ruled surfaces are the unique Hirzebruch surfaces
`X_e=P_P1(O direct-sum O(-e))`, `e>=0`, and normalized rank-two bundles on
`P^1` split.

Theorem 2.15 classifies indecomposable elliptic ruled surfaces: their
invariant is zero or minus one, with one ruled surface of each kind. The
printed proof invokes a ramified degree-two pencil with the parenthetical
`assume char k != 2`, although the theorem is stated under the chapter's
arbitrary-characteristic convention. The all-characteristic theorem therefore
needs the exact Atiyah source or a replacement proof. Corollary 2.16 gives
Atiyah's parametrization of rank-two indecomposable bundles of fixed degree
by the elliptic curve. Caution 2.15.1 records that a nonsplit extension of line
bundles can nevertheless have decomposable middle term.

Remark 2.16.1 points to the general stable-bundle theory and
Narasimhan–Seshadri. Its phrase “nice algebraic families” is contextual rather
than a proof specification; the precise stability criterion actually used is
isolated from Exercise 2.8(a,b).

## Rational ruled surfaces and scrolls, printed pp.379–381

For `X_e`, Theorem 2.17 determines exactly when a section of class `C_0+nf`
exists and when its complete system is basepoint-free or very ample:

- a section exists exactly for `n=0` or `n>=e`;
- basepoint-free exactly when `n>=e`;
- very ample exactly when `n>e`.

Corollary 2.18 gives the ample cone and classifies divisor classes containing
irreducible or smooth irreducible members. Corollary 2.19 embeds `X_e`, for
`n>e`, as a rational scroll of degree `d=2n-e` in `P^(d+1)` and records the
quadric, cubic, and two quartic-scroll examples.

Remark 2.19.2 quotes Nagata's classification: a smooth nondegenerate surface
of degree `d` in `P^(d+1)` is a rational scroll, a plane, or the Veronese
surface. This external theorem is a source blocker.

## Ample cones over a general base, printed pp.382–383

For `e>=0`, Proposition 2.20 proves that an irreducible curve
`aC_0+bf`, other than `C_0` and a fibre, has `a>0` and `b>=ae`; a divisor of
that type is ample exactly when `a>0` and `b>ae`.

For `e<0`, assuming either characteristic zero or `g<=1`, Proposition 2.21
proves the sharper irreducible-curve alternatives

`a=1,b>=0`, or `a>=2,b>=a*e/2`,

and the ample criterion `a>0`, `b>a*e/2`. The proof uses Hurwitz and
adjunction. The positive-characteristic higher-genus extensions in Exercises
2.14–2.15 and the very-ampleness refinements in Exercises 2.11–2.12 are
explicitly outside the adopted exercise scope.

## Exercise disposition, printed pp.383–386

- **Exercises 2.1–2.2 — OUT.** Birational uniqueness of the base curve and
  the disjoint-section criterion for decomposability have no later included
  running-text dependency.
- **Exercise 2.3(a) — ADOPTED; (b) OUT.** The arbitrary-rank filtration by
  invertible successive quotients is asserted in Remark 2.7.1. Its printed
  hint activates II Exercise 8.2. The higher-dimensional counterexample in
  (b) is not used.
- **Exercises 2.4–2.5 — OUT.** The possible self-intersections of sections and
  the sharper existence bounds for `e` are optional extensions, not inputs to
  the included running proofs. The Nagata lower bound in the note to 2.5 is
  recorded as external context only.
- **Exercise 2.6 — ADOPTED.** Full Birkhoff–Grothendieck splitting is the
  arbitrary-rank assertion cited in Corollary 2.14 and Remark 2.16.1.
- **Exercise 2.7 — OUT.** The family of square-one sections on the elliptic
  example is not used later.
- **Exercise 2.8(a,b) — ADOPTED; (c) OUT.** The decomposable obstruction and
  normalized rank-two stability criterion supply the precise content cited in
  Remark 2.16.1. The classification of nonsemistable bundles in (c) is not
  needed.
- **Exercise 2.9 — ADOPTED.** Its even/odd degree and genus formulas for a
  smooth curve on a quadric cone are quoted in running Remark IV.6.4.1(d).
  The formerly untagged forward leaf is reconciled to this source unit.
- **Exercises 2.10–2.17 — OUT.** Exercise 2.10 is an alternative construction
  mentioned after Kleiman–Laksov already proves the IV.5 existence claim.
  Exercises 2.11–2.12 and 2.14–2.15 elaborate remarks without entering a
  later included proof; 2.13, 2.16, and 2.17 likewise have no later running
  dependency.

No later running text in Chapter V or Appendices A–C cites a V.2 exercise.

## Reactivated earlier prerequisite

Exercise 2.3(a) explicitly uses II Exercise 8.2: on an `n`-dimensional
variety, a globally generated vector bundle of rank greater than `n` admits a
nowhere-vanishing section with locally free quotient. This clause is now a
separate leaf tagged to `chapter-ii-section-8`; no other earlier exercise is
newly activated.

## External sources, blockers, and context

- The twist classification of projectivizations inherits the existing II.7
  blocker for the Picard group of a projective bundle; it is not a new V.2
  source root.
- The arbitrary-characteristic elliptic ruled-surface classification needs an
  exact passage from Atiyah [1], or another proof that repairs the
  characteristic-two gap in Hartshorne's argument.
- Nagata [5], I, Theorem 7, is required for the minimal-degree surface
  classification in Remark 2.19.2.
- The Tsen/Shafarevich section-existence note is contextual: the adopted
  definition already includes a section. The general stable-moduli sentence
  and the Nagata bound in excluded Exercise 2.5 are also recorded as context,
  not formal leaves.

Thus V.2 has two new explicit source blockers and one inherited II.7 blocker.

## Pinned Mathlib audit and false friends

The pinned checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). No V.2 leaf is an
exact pinned-Mathlib result.

Recent useful infrastructure includes `SheafOfModules.IsLocallyFree`, added
in June 2026, and the algebraic theorem that finite flat modules of constant
stalk rank are locally free in `RingTheory/Flat/LocallyFree.lean`. These do
not provide rank, degree, normalization, stability, or classification of
vector bundles on curves.

`AlgebraicGeometry.ProjectiveSpectrum` is absolute `Proj` of a graded ring,
not relative `P(E)` with its tautological quotient, section functor, Picard
group, twist classification, or pushforward formulas. The topological and
manifold `VectorBundle` namespaces and analytic `Slope` APIs are unrelated.
There is no ruled or Hirzebruch surface, Birkhoff–Grothendieck theorem, Atiyah
classification, bundle-stability theorem, ruled intersection calculation, or
ruled ample-cone criterion in pinned Mathlib.

## Representation choices and warnings

- Use Hartshorne's quotient convention
  `P(E)=Proj_C Sym(E)`, with tautological quotient `pi^*E -> O(1)` and
  `pi_*O(1)=E`. Reversing to the line-subbundle convention changes every
  twist and section formula.
- Distinguish the divisor `epsilon` with `det E=O_C(epsilon)` from the integer
  invariant `e=-deg E`. Similarly distinguish a base divisor `b` from its
  degree when writing numerical classes `aC_0+b f`.
- Normalization determines `deg E` and `e`, not necessarily the normalized
  bundle or distinguished section uniquely.
- Keep `Pic X ~= Z direct-sum pi^*Pic C` separate from the numerical lattice
  generated by `C_0,f`.
- Stability uses quotient slopes in Hartshorne's convention; translate
  carefully to the more common subsheaf convention.
- Do not use the characteristic-not-two proof of Theorem 2.15 as an
  arbitrary-characteristic specification.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Ruled-surface definition and product example | `surfaces/ruled-surfaces/foundations/geometrically-ruled-surface.md` |
| Fibres form an algebraic family | `surfaces/ruled-surfaces/foundations/ruled-fibres-algebraically-equivalent.md` |
| Fibres are numerically equivalent | `surfaces/ruled-surfaces/foundations/ruled-fibres-numerically-equivalent.md` |
| Lemma 2.1, nonnegative fibre degree | `surfaces/ruled-surfaces/foundations/ruled-pushforward-nonnegative-fibre-degree.md` |
| Lemma 2.1, structure sheaf | `surfaces/ruled-surfaces/foundations/ruled-pushforward-structure-sheaf.md` |
| Ruled surface is a projective bundle | `surfaces/ruled-surfaces/foundations/ruled-surface-projective-bundle-presentation.md` |
| Rank-two projective bundle is ruled | `surfaces/ruled-surfaces/foundations/rank-two-projective-bundle-is-ruled.md` |
| Birational product | `surfaces/ruled-surfaces/foundations/ruled-surface-birational-product.md` |
| Proposition 2.3, Picard group | `surfaces/ruled-surfaces/foundations/ruled-surface-picard-decomposition.md` |
| Proposition 2.3, numerical lattice | `surfaces/ruled-surfaces/foundations/ruled-surface-numerical-intersection-basis.md` |
| Lemma 2.4, higher-direct-image vanishing | `surfaces/ruled-surfaces/foundations/ruled-line-bundle-higher-direct-image-vanishing.md` |
| Lemma 2.4, Leray comparison | `surfaces/ruled-surfaces/foundations/ruled-line-bundle-leray-comparison.md` |
| Corollary 2.5 | `surfaces/ruled-surfaces/foundations/ruled-surface-cohomological-invariants.md` |
| Sections and invertible quotients | `surfaces/ruled-surfaces/normalization/projective-bundle-sections-quotient-lines.md` |
| Proposition 2.6 kernel formula | `surfaces/ruled-surfaces/normalization/section-kernel-formula.md` |
| Corollary 2.7 | `surfaces/ruled-surfaces/normalization/rank-two-bundle-line-extension.md` |
| Normalized bundle existence | `surfaces/ruled-surfaces/normalization/normalized-projective-bundle-existence.md` |
| The invariant `e` | `surfaces/ruled-surfaces/normalization/normalized-ruled-surface-invariant.md` |
| Distinguished normalized section | `surfaces/ruled-surfaces/normalization/normalized-tautological-section.md` |
| Proposition 2.9 | `surfaces/ruled-surfaces/normalization/section-divisor-class-intersection.md` |
| Lemma 2.10 | `surfaces/ruled-surfaces/normalization/ruled-surface-canonical-divisor.md` |
| Corollary 2.11 | `surfaces/ruled-surfaces/normalization/ruled-surface-canonical-number.md` |
| Examples 2.11.1–3 | `surfaces/ruled-surfaces/normalization/decomposable-normalized-examples.md` |
| Examples 2.11.4–5 | `surfaces/ruled-surfaces/normalization/cone-blowup-ruled-surface.md` |
| Example 2.11.6 | `surfaces/ruled-surfaces/normalization/elliptic-negative-one-extension.md` |
| Theorem 2.12(a) | `surfaces/ruled-surfaces/classification/normalized-decomposable-bundles.md` |
| Theorem 2.12(b) | `surfaces/ruled-surfaces/classification/indecomposable-invariant-bounds.md` |
| Corollaries 2.13–2.14 | `surfaces/ruled-surfaces/classification/rational-ruled-surface-classification.md` |
| Elliptic invariant zero | `surfaces/ruled-surfaces/classification/elliptic-indecomposable-e-zero.md` |
| Elliptic invariant minus one | `surfaces/ruled-surfaces/classification/elliptic-indecomposable-e-minus-one.md` |
| Elliptic invariant minus two is impossible | `surfaces/ruled-surfaces/classification/elliptic-e-minus-two-impossible.md` |
| Theorem 2.15 | `surfaces/ruled-surfaces/classification/elliptic-ruled-surface-classification.md` |
| Corollary 2.16 and Caution 2.15.1 | `surfaces/ruled-surfaces/classification/atiyah-rank-two-classification-extension-caution.md` |
| Theorem 2.17(a) | `surfaces/ruled-surfaces/rational-scrolls/rational-section-existence.md` |
| Theorem 2.17(b) | `surfaces/ruled-surfaces/rational-scrolls/rational-basepoint-free-sections.md` |
| Theorem 2.17(c) | `surfaces/ruled-surfaces/rational-scrolls/rational-very-ample-sections.md` |
| Corollary 2.18(a) | `surfaces/ruled-surfaces/rational-scrolls/rational-ample-cone.md` |
| Corollary 2.18(b) | `surfaces/ruled-surfaces/rational-scrolls/rational-irreducible-member-criterion.md` |
| Corollary 2.19 and examples | `surfaces/ruled-surfaces/rational-scrolls/rational-scroll-embedding-examples.md` |
| Remark 2.19.2 | `surfaces/ruled-surfaces/rational-scrolls/nagata-minimal-degree-surface-classification.md` |
| Proposition 2.20(a) | `surfaces/ruled-surfaces/ample-cones/nonnegative-e-irreducible-curve-bound.md` |
| Proposition 2.20(b) | `surfaces/ruled-surfaces/ample-cones/nonnegative-e-ample-cone.md` |
| Proposition 2.21(a) | `surfaces/ruled-surfaces/ample-cones/negative-e-irreducible-curve-bound.md` |
| Proposition 2.21(b) | `surfaces/ruled-surfaces/ample-cones/negative-e-ample-cone.md` |
| Exercise 2.3(a) | `surfaces/ruled-surfaces/exercises/vector-bundle-successive-line-extensions.md` |
| Exercise 2.6 | `surfaces/ruled-surfaces/exercises/birkhoff-grothendieck-splitting.md` |
| Exercise 2.8(a,b) | `surfaces/ruled-surfaces/exercises/normalized-rank-two-stability.md` |
| Exercise 2.9 | `surfaces/ruled-surfaces/exercises/quadric-cone-curve-degree-genus.md` |

## Reactivated-prerequisite map

| Source result | Roadmap article |
|---|---|
| II Exercise 8.2 | `surfaces/prerequisites/globally-generated-bundle-nowhere-vanishing-section.md` |
