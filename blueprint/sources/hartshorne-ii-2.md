# Hartshorne II.2: Schemes

Robin Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics 52,
Springer, 1977, Chapter II, §2, printed pp. 69–82.  In the repository scan the
one-based PDF page is the printed page plus 15, so this span is PDF pages
84–97.  All locators below are printed page numbers and were checked against
the repository PDF.

This note is the detailed source contract for the four §II.2 roadmap chapters.
The running mathematical text is adopted in full.  An exercise is adopted
when approved running text cites it, delegates a proof to it, or later uses
it; the disposition is recorded below.

## Running-text inventory

### Opening and Lemma 2.1

Printed pp. 69–70.  The section announces `Spec A`, schemes locally affine in
that sense, `Proj S`, and the comparison with Chapter I varieties.  For an
ideal `𝔞 ⊆ A`, `V(𝔞)` is the set of primes containing `𝔞`.  Lemma 2.1 proves
`V(𝔞𝔟) = V(𝔞) ∪ V(𝔟)`, `V(Σ 𝔞ᵢ) = ⋂ V(𝔞ᵢ)`, and
`V(𝔞) ⊆ V(𝔟) ↔ √𝔞 ⊇ √𝔟`; these sets define the Zariski topology.  The
principal opens `D(f)` form a basis.

### Structure sheaf and Proposition 2.2

Printed pp. 70–72.  A section on `U ⊆ Spec A` is a dependent function with
value in `A_𝔭` at `𝔭`, locally represented by a quotient `a/f` with the
denominator outside every prime in the chosen neighbourhood.  Proposition 2.2
identifies the stalk at `𝔭` with `A_𝔭`, the sections on `D(f)` with `A_f`, and
the global sections with `A`.  The proof of the basic-open assertion uses
quasi-compactness of `D(f)` and a common-power denominator argument.

### Locally ringed spaces and Proposition 2.3

Printed pp. 72–74.  A ringed space is a space with a sheaf of rings.  It is
locally ringed when every stalk is local.  A morphism consists of a continuous
map and a map `𝒪_Y → f_*𝒪_X`, and it is a morphism of locally ringed spaces when
every induced stalk map is local.  Proposition 2.3 says `Spec A` is locally
ringed, a ring homomorphism `A → B` induces `Spec B → Spec A`, and every
morphism between affine spectra arises uniquely this way.  Caution 2.3.0
explains that locality on stalks is essential for the converse.

### Schemes and gluing

Printed pp. 74–76.  An affine scheme is a locally ringed space isomorphic to a
spectrum.  A scheme is a locally ringed space admitting affine neighbourhoods
at every point, and scheme morphisms are locally-ringed-space morphisms.
Examples 2.3.1–2.3.4 describe spectra of a field, a DVR, the affine line, and
the affine plane.  Example 2.3.5 glues two schemes along isomorphic open
subschemes by gluing both the underlying spaces and compatible sections.
Example 2.3.6 constructs the affine line with doubled origin.

### Proj, Lemma 2.4, and Proposition 2.5

Printed pp. 76–77.  For an `ℕ`-graded ring `S`, `Proj S` consists of homogeneous
prime ideals not containing the irrelevant ideal `S₊`.  Homogeneous zero loci
define its topology.  Its structure sheaf consists locally of degree-zero
fractions of same-degree homogeneous elements.  Lemma 2.4 supplies the
zero-locus identities.  Proposition 2.5 identifies the stalk with `S_(𝔭)`,
identifies `D₊(f)` with `Spec S_(f)` for homogeneous positive-degree `f`, and
concludes that `Proj S` is a scheme.  Example 2.5.1 defines
`ℙⁿ_A = Proj A[x₀,…,xₙ]`.

### Schemes over a base and Proposition 2.6

Printed pp. 78–79.  A scheme over `S` is a scheme with a morphism to `S`; an
`S`-morphism commutes with the structure maps.  Proposition 2.6 constructs a
fully faithful functor from varieties over an algebraically closed field `k`
to schemes over `k`.  For a space `X`, Hartshorne's `t(X)` is the set of
nonempty irreducible closed subsets, topologized so the closed sets are
`t(Y)` for closed `Y ⊆ X`; `α_X(x) = closure {x}` induces a bijection on open
sets.  For a variety `V`, the associated ringed space is
`(t(V), α_{V*}𝒪_V)`.  In the affine case, prime ideals of the coordinate ring
identify this with `Spec A(V)`; affine covers give the general scheme.  The
constant functions give the map to `Spec k`.  Exercise 2.15 supplies the final
closed-point and full-faithfulness checks.

## Adopted exercises

The exercises themselves are printed on pp. 79–82.

### Exercises 2.1 through 2.9

- **2.1:** `D(f)` with its induced scheme structure is `Spec A_f`.  Used in
  the affine-local arguments beginning with Proposition 3.2, p. 83.
- **2.2:** every open subset of a scheme is a scheme.  Invoked on p. 85.
- **2.3(a) only:** a scheme is reduced iff all its local rings are reduced.
  Invoked in the definition on p. 82.  Parts (b),(c), constructing the reduced
  scheme and its universal property, are not used by later running text here.
- **2.4:** morphisms `X → Spec A` correspond to ring maps
  `A → Γ(X,𝒪_X)`.  Used in the product construction on p. 87 and later.
- **2.5:** `Spec ℤ` is terminal.  Used to define absolute products on p. 87.
- **2.7:** maps `Spec K → X` are a point `x` together with an embedding
  `κ(x) → K`.  Used to define fibres on p. 89.
- **2.8:** maps from the dual numbers over `k` through a `k`-rational point
  correspond to tangent vectors.  Invoked in deformation theory on p. 265 and
  in the smoothness discussion on p. 270.
- **2.9:** every nonempty irreducible closed subset of a scheme has a unique
  generic point.  The running comparison paragraph already invokes it on
  p. 77.

### Exercises 2.12 through 2.19

- **2.12:** general scheme gluing.  Used for products on p. 88 and relative
  Proj on p. 160.
- **2.13(a–d):** Noetherian spaces are characterized by quasi-compact opens;
  affine schemes are quasi-compact; a Noetherian ring has Noetherian spectrum;
  and the converse fails.  These support the definition and caution on
  pp. 82–83 and Proposition 3.2.
- **2.14(b–d):** a graded homomorphism gives a morphism from its natural open
  domain on `Proj`; an eventual degreewise isomorphism gives an isomorphism of
  Proj schemes; and a projective variety completes to the Proj of its
  homogeneous coordinate ring.  Later running text uses graded functoriality
  on p. 117 and tail invariance on p. 120; part (d) is also the promised
  comparison in Example 2.5.1 and Proposition 2.6.
- **2.15(a–c):** closed points of an associated variety scheme are precisely
  the `k`-rational points, scheme morphisms over `k` preserve them, and the
  comparison functor is fully faithful.  Proposition 2.6 explicitly delegates
  its final assertion to this exercise on p. 79.
- **2.16(a–d):** the nonvanishing locus of a global section is open; vanishing
  on it gives power torsion under quasi-compactness; under the stated finite
  affine-intersection hypothesis sections acquire a common power denominator;
  hence `Γ(X_f,𝒪) ≅ Γ(X,𝒪)_f`.  Part (a) is used in Proposition 3.1 on p. 82,
  and the package is generalized in Lemma 5.14 on p. 118.
- **2.17(a,b):** isomorphisms are local on the target, and the finite
  principal-open affineness criterion.  The latter is used in Serre's
  affineness criterion on pp. 215–216.
- **2.18(a,c):** `D(f)` is empty iff `f` is nilpotent, and a surjective ring map
  induces a closed immersion of spectra with surjective structure-sheaf map.
  Used on pp. 82 and 85, and again for nilpotence in Proposition II.9.5 on
  p. 197. Parts (b),(d) are not adopted by the running-text rule.
- **2.19:** disconnected spectrum, a nontrivial orthogonal-idempotent
  decomposition, and a nontrivial product decomposition of the ring are
  equivalent.  Used in Theorem III.11.3 on p. 280, immediately before
  Zariski's Main Theorem, Corollary III.11.4.

## Pinned Mathlib audit

The pinned checkout is Mathlib `v4.33.1`, commit
`0df444a360eaa60ab8c11dca51a86af692955474`.  Exact declarations are named in
the individual roadmap leaves.  The principal implementation files are:

- `Mathlib/RingTheory/Spectrum/Prime/Basic.lean` and `Topology.lean`;
- `Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean`;
- `Mathlib/AlgebraicGeometry/StructureSheaf.lean`, `Spec.lean`,
  `GammaSpecAdjunction.lean`, `Scheme.lean`, `AffineScheme.lean`,
  `Restrict.lean`, and `Gluing.lean`;
- `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.lean`,
  `StructureSheaf.lean`, `Scheme.lean`, `Basic.lean`, and `Functor.lean`;
- `Mathlib/AlgebraicGeometry/Over.lean`, `ResidueField.lean`, `Limits.lean`,
  `Properties.lean`, `Noetherian.lean`, and the relevant morphism files.

The foundational spectrum, scheme, gluing, and Proj results are exact upstream
matches.  Mathlib contributors named in these files include Johan Commelin,
Kim Morrison, Andrew Yang, Justus Springer, Jujian Zhang, and Kenny Lau.

## Representation decisions and gaps

1. Use Mathlib's bundled `Scheme`, whose local-affineness proof is part of the
   object, and its predicate `IsAffine`; do not introduce a parallel scheme
   structure.
2. Use `Scheme.Opens.toScheme` for open subschemes and categorical
   `CategoryTheory.Over S` (with `Scheme.Over`/`Hom.IsOver` wrappers) for
   schemes over a base.
3. Represent Hartshorne's `S_(f)` and `S_(𝔭)` by
   `HomogeneousLocalization.Away 𝒜 f` and
   `HomogeneousLocalization.AtPrime 𝒜 𝔭`.  Mathlib's Proj takes an explicit
   `ℕ`-graded decomposition `𝒜 : ℕ → σ`.
4. Give the scheme `ℙⁿ_A` a name distinct from the project's existing
   classical-point `Hartshorne.ProjectiveSpace`.
5. The current project `Variety` structure is more general than Hartshorne's
   four classes and does not itself imply local affineness.  Proposition 2.6
   therefore uses the existing `Variety.HasAffineOpenBasis`, already proved for
   affine, quasi-affine, projective, and quasi-projective constructors.
6. Mathlib's `Proj.map` assumes `T₊ ≤ map φ S₊`, so it gives a map on all of
   `Proj T`.  It is not the full Exercise 2.14(b), which defines a map only on
   `U = {𝔭 | 𝔭 ⊉ φ(S₊)}` for an arbitrary graded homomorphism.
7. No exact pinned theorem was found for the dual-number tangent-vector
   equivalence, eventual-degree Proj invariance, the non-Noetherian-ring
   counterexample, or the connected-spectrum/idempotent/product equivalence.

## Excluded and deferred material

- Exercises 2.3(b,c), 2.6, 2.10, 2.11, 2.14(a), and 2.18(b,d) are outside
  this milestone because approved running text neither cites them, delegates
  a proof to them, nor later uses them.
- Examples 2.3.1–2.3.4 are explanatory instances of exact upstream
  constructions and receive no separate leaves.
- The doubled-origin construction of Example 2.3.6 is explanatory here.  Its
  nonseparatedness belongs to §II.4; its asserted nonaffineness is deferred
  with that example.
- No claim is made that the excluded exercises are mathematically
  unimportant—only that later adopted running text does not require them at
  this boundary.
