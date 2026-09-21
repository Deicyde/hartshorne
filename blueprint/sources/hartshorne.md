# Hartshorne, *Algebraic Geometry*

Robin Hartshorne, *Algebraic Geometry*, Springer, Graduate Texts in Mathematics
52, 1977. ISBN 978-1-4757-3849-0.

The book is not redistributed with this repository. Locators below are **printed
book page numbers**, which is the numbering the text itself uses in cross
references. If you are reading a scan whose front matter is included, the
1977 Springer printing has `pdf page index = book page + 15`, so book page 1
(the first page of Chapter I) is the sixteenth page of the file. Checked
against book pages 12, 13, 22, 23 and 24.

Results Hartshorne numbers with a trailing `A` (1.3A, 1.8A, 1.11A, …) are
commutative algebra he quotes without proof and attributes to Atiyah–Macdonald,
Matsumura, or Zariski–Samuel. In this roadmap they carry `origin: background`:
they are prerequisites to satisfy from Mathlib or to prove separately, not
targets this project claims from the source.

## I.1

Affine Varieties, book pp. 1–8.

| Locator | Statement | Page | Roadmap article |
| --- | --- | --- | --- |
| Def. | Affine `n`-space `𝔸ⁿ`; zero set `Z(T)`; algebraic set | 1–2 | [Algebraic sets](../roadmap/affine-varieties/algebraic-set.md) |
| Prop. 1.1 | Finite unions and arbitrary intersections of algebraic sets are algebraic; `∅` and `𝔸ⁿ` are algebraic | 2 | [Zariski topology](../roadmap/affine-varieties/zariski-topology.md) |
| Def. | Zariski topology on `𝔸ⁿ` | 2 | [Zariski topology](../roadmap/affine-varieties/zariski-topology.md) |
| Def. | Irreducible subset of a topological space | 3 | [Affine varieties](../roadmap/affine-varieties/affine-variety.md) |
| Def. | Affine variety; quasi-affine variety | 3 | [Affine varieties](../roadmap/affine-varieties/affine-variety.md) |
| Def. | Ideal `I(Y)` of a subset of `𝔸ⁿ` | 3 | [Vanishing ideal](../roadmap/affine-varieties/vanishing-ideal.md) |
| Prop. 1.2 | `Z`/`I` order reversal, `I(Y₁ ∪ Y₂) = I(Y₁) ∩ I(Y₂)`, `I(Z(𝔞)) = √𝔞`, `Z(I(Y)) = Ȳ` | 3 | [Vanishing ideal](../roadmap/affine-varieties/vanishing-ideal.md), [Nullstellensatz](../roadmap/affine-varieties/nullstellensatz.md) |
| Thm. 1.3A | Hilbert's Nullstellensatz | 4 | [Nullstellensatz](../roadmap/affine-varieties/nullstellensatz.md) |
| Cor. 1.4 | Algebraic sets ↔ radical ideals, inclusion-reversing; irreducible ↔ prime | 4 | [Radical ideal correspondence](../roadmap/affine-varieties/radical-ideal-correspondence.md) |
| Def. | Affine coordinate ring `A(Y) = A/I(Y)` | 4 | [Affine coordinate ring](../roadmap/affine-varieties/affine-coordinate-ring.md) |
| Rmk. 1.4.6 | `A(Y)` is a f.g. `k`-algebra and a domain; conversely every such ring arises | 4–5 | [Affine coordinate ring](../roadmap/affine-varieties/affine-coordinate-ring.md) |
| Def. | Noetherian topological space | 5 | [Affine space is Noetherian](../roadmap/affine-varieties/affine-space-noetherian.md) |
| Ex. 1.4.7 | `𝔸ⁿ` is a Noetherian topological space | 5 | [Affine space is Noetherian](../roadmap/affine-varieties/affine-space-noetherian.md) |
| Prop. 1.5 | Every nonempty closed subset of a Noetherian space is a finite irredundant union of irreducible closed subsets, uniquely | 5 | [Irreducible decomposition](../roadmap/affine-varieties/irreducible-decomposition.md) |
| Cor. 1.6 | Every algebraic set in `𝔸ⁿ` is uniquely a union of varieties, none containing another | 5 | [Irreducible decomposition](../roadmap/affine-varieties/irreducible-decomposition.md) |
| Def. | Dimension of a topological space; height of a prime; Krull dimension | 5–6 | [Dimension](../roadmap/affine-varieties/dimension.md) |
| Prop. 1.7 | `dim Y = dim A(Y)` for an affine algebraic set | 6 | [Dimension via the coordinate ring](../roadmap/affine-varieties/dim-eq-coordinate-ring-dim.md) |
| Thm. 1.8A(a) | For a f.g. `k`-algebra domain `B`: `dim B = trdeg_k K(B)` | 6 | [Dimension of a finitely generated domain](../roadmap/affine-varieties/dim-fg-domain.md) |
| Thm. 1.8A(b) | For a f.g. `k`-algebra domain `B`: `height 𝔭 + dim B/𝔭 = dim B` | 6 | [The dimension formula](../roadmap/affine-varieties/dim-formula-catenary.md) |
| Prop. 1.9 | `dim 𝔸ⁿ = n` | 6 | [Dimension of affine space](../roadmap/affine-varieties/dim-affine-space.md) |
| Prop. 1.10 | `dim Y = dim Ȳ` for `Y` quasi-affine | 6 | [Dimension of a quasi-affine variety](../roadmap/affine-varieties/dim-quasi-affine.md) |
| Thm. 1.11A | Krull's Hauptidealsatz | 7 | [Hypersurfaces and codimension one](../roadmap/affine-varieties/hypersurface-dimension.md) |
| Prop. 1.12A | A Noetherian domain is a UFD iff every height-one prime is principal | 7 | [Hypersurfaces and codimension one](../roadmap/affine-varieties/hypersurface-dimension.md) |
| Prop. 1.13 | A variety in `𝔸ⁿ` has dimension `n − 1` iff it is `Z(f)` for an irreducible nonconstant `f` | 7 | [Hypersurfaces and codimension one](../roadmap/affine-varieties/hypersurface-dimension.md) |

## I.2

Projective Varieties, book pp. 8–14.

Hartshorne states only 2.1, 2.2 and 2.3 in the running text and leaves the
projective analogues of the §1 correspondence to Exercises 2.1–2.7. Those
exercise results are used by §3 and later chapters, so this roadmap treats them
as source targets rather than optional practice.

| Locator | Statement | Page | Roadmap article |
| --- | --- | --- | --- |
| Def. | Projective `n`-space `ℙⁿ`; homogeneous coordinates | 8–9 | [Projective space](../roadmap/projective-varieties/projective-space.md) |
| Def. | Graded ring; homogeneous element; homogeneous ideal; the grading on `S = k[x₀,…,xₙ]` | 9 | [Homogeneous ideals](../roadmap/projective-varieties/homogeneous-ideal.md) |
| Def. | `Z(T)` for a set `T` of homogeneous elements; algebraic set in `ℙⁿ` | 9 | [Projective algebraic sets](../roadmap/projective-varieties/projective-algebraic-set.md) |
| Prop. 2.1 | Finite unions and arbitrary intersections of algebraic sets in `ℙⁿ` are algebraic | 9 | [Projective algebraic sets](../roadmap/projective-varieties/projective-algebraic-set.md) |
| Def. | Zariski topology on `ℙⁿ` | 10 | [Projective Zariski topology](../roadmap/projective-varieties/projective-zariski-topology.md) |
| Def. | Projective variety; quasi-projective variety; their dimension | 10 | [Projective varieties](../roadmap/projective-varieties/projective-variety.md) |
| Def. | Homogeneous ideal `J(Y)`; homogeneous coordinate ring `S(Y) = S/J(Y)` | 10 | [Homogeneous vanishing ideal](../roadmap/projective-varieties/homogeneous-vanishing-ideal.md) |
| Prop. 2.2 | `φᵢ : Uᵢ → 𝔸ⁿ` is a homeomorphism | 10–11 | [Standard affine charts](../roadmap/projective-varieties/standard-affine-charts.md) |
| Cor. 2.3 | Every projective (quasi-projective) variety is covered by affine (quasi-affine) varieties `Y ∩ Uᵢ` | 11 | [Affine cover](../roadmap/projective-varieties/affine-cover.md) |
| Ex. 2.1 | Homogeneous Nullstellensatz | 11 | [Projective Nullstellensatz](../roadmap/projective-varieties/projective-nullstellensatz.md) |
| Ex. 2.2 | `Z(𝔞) = ∅` iff `√𝔞` is `S` or `S₊`, iff `𝔞 ⊇ S_d` for some `d > 0` | 11 | [Homogeneous ideal correspondence](../roadmap/projective-varieties/homogeneous-ideal-correspondence.md) |
| Ex. 2.3 | `Z`/`J` order reversal, `J(Y₁ ∪ Y₂) = J(Y₁) ∩ J(Y₂)`, `Z(J(Y)) = Ȳ` | 11 | [Homogeneous vanishing ideal](../roadmap/projective-varieties/homogeneous-vanishing-ideal.md) |
| Ex. 2.4 | Algebraic sets in `ℙⁿ` ↔ homogeneous radical ideals `≠ S₊`; irreducible ↔ prime; `ℙⁿ` is irreducible | 11 | [Homogeneous ideal correspondence](../roadmap/projective-varieties/homogeneous-ideal-correspondence.md) |
| Ex. 2.5 | `ℙⁿ` is a Noetherian topological space; irreducible components exist and are unique | 11 | [Projective space is Noetherian](../roadmap/projective-varieties/projective-space-noetherian.md) |
| Ex. 2.6 | `dim S(Y) = dim Y + 1` for a projective variety `Y` | 11–12 | [Homogeneous coordinate ring dimension](../roadmap/projective-varieties/homogeneous-coordinate-ring-dimension.md) |
| Ex. 2.7 | `dim ℙⁿ = n`; `dim Y = dim Ȳ` for `Y` quasi-projective | 12 | [Dimension in projective space](../roadmap/projective-varieties/projective-dimension.md) |

## I.3

Morphisms, book pp. 14–23.

| Locator | Statement | Page | Roadmap article |
| --- | --- | --- | --- |
| Def. | Regular function on a quasi-affine variety | 15 | [Regular functions, quasi-affine](../roadmap/morphisms/regular-function-quasi-affine.md) |
| Lem. 3.1 | A regular function is continuous | 15 | [Regular functions are continuous](../roadmap/morphisms/regular-function-continuous.md) |
| Def. | Regular function on a quasi-projective variety | 15 | [Regular functions, quasi-projective](../roadmap/morphisms/regular-function-quasi-projective.md) |
| Rmk. 3.1.1 | Two regular functions agreeing on a nonempty open subset agree everywhere | 15 | [Regular functions are continuous](../roadmap/morphisms/regular-function-continuous.md) |
| Def. | Variety over `k` | 15 | [Varieties](../roadmap/morphisms/variety.md) |
| Def. | Morphism; isomorphism of varieties | 15–16 | [Morphisms](../roadmap/morphisms/morphism.md) |
| Def. | Ring of global regular functions `𝒪(Y)` | 16 | [Ring of regular functions](../roadmap/morphisms/ring-of-regular-functions.md) |
| Def. | Local ring `𝒪_{P,Y}` of germs at `P` | 16 | [Local ring at a point](../roadmap/morphisms/local-ring.md) |
| Def. | Function field `K(Y)`; rational functions | 16 | [Function field](../roadmap/morphisms/function-field.md) |
| After Defs. | Natural injective homomorphisms `𝒪(Y) → 𝒪_{P,Y} → K(Y)` and `𝒪(Y) = ⋂_{P ∈ Y} 𝒪_{P,Y}` inside `K(Y)` | 16 | [Underlying injections](../roadmap/morphisms/function-field-injections.md), [Intersection of local rings](../roadmap/morphisms/global-functions/global-regular-intersection-local-rings.md) |
| Thm. 3.2(a) | For `Y` affine: `𝒪(Y) ≅ A(Y)` | 17 | [Coordinate ring is the ring of regular functions](../roadmap/morphisms/global-regular-eq-coordinate-ring.md) |
| Thm. 3.2(b) | Points of `Y` ↔ maximal ideals of `A(Y)` | 17 | [Points and maximal ideals](../roadmap/morphisms/points-eq-maximal-ideals.md) |
| Thm. 3.2(c),(d) | `𝒪_P ≅ A(Y)_{𝔪_P}` with `dim 𝒪_P = dim Y`; `K(Y) ≅ Frac A(Y)` of transcendence degree `dim Y` | 17 | [Local ring and function field](../roadmap/morphisms/affine-variety-rings.md) |
| Prop. 3.3 | `φᵢ : Uᵢ → 𝔸ⁿ` is an isomorphism of varieties | 18 | [Charts are isomorphisms](../roadmap/morphisms/projective-rings/chart-isomorphism.md) |
| Def. | Graded localizations `S_(𝔭)` and `S_(f)` | 18 | [Graded localization](../roadmap/morphisms/projective-rings/graded-localization.md) |
| Thm. 3.4 | For `Y` projective: `𝒪(Y) = k`; `𝒪_P = S(Y)_(𝔪_P)`; `K(Y) ≅ S(Y)_((0))` | 18–19 | [(a)](../roadmap/morphisms/projective-rings/projective-global-regular.md), [(b)](../roadmap/morphisms/projective-rings/projective-local-ring.md), [(c)](../roadmap/morphisms/projective-rings/projective-function-field.md) |
| Prop. 3.5 | `Hom(X, Y) ≅ Hom_{k-alg}(A(Y), 𝒪(X))` for `Y` affine, `X` any variety | 19 | [Morphisms into an affine variety](../roadmap/morphisms/hom-affine-bijection.md) |
| Lem. 3.6 | `ψ : X → Y ⊆ 𝔸ⁿ` is a morphism iff each `xᵢ ∘ ψ` is regular | 20 | [Criterion for a morphism to an affine variety](../roadmap/morphisms/morphism-to-affine-criterion.md) |
| Cor. 3.7 | Affine varieties `X`, `Y` are isomorphic iff `A(X) ≅ A(Y)` as `k`-algebras | 20 | [Isomorphism via coordinate rings](../roadmap/morphisms/affine-iso-iff-algebra-iso.md) |
| Cor. 3.8 | `X ↦ A(X)` is an arrow-reversing equivalence between affine varieties over `k` and finitely generated integral domains over `k` | 20 | [Equivalence with finitely generated domains](../roadmap/morphisms/affine-variety-equivalence.md) |
| Thm. 3.9A | Finiteness of integral closure | 20 | **No article.** Hartshorne states it in §3 with "we include here an algebraic result which will be used in the exercises"; nothing in the main text of §§1–3 uses it, and the exercises that do are out of scope. It is needed from §6 onward. |

## I.4

Rational Maps, book pp. 24–31; the running text is pp. 24–29 and the exercises
begin on p. 30.

Two results the main text uses are stated as exercises in earlier sections and
were previously out of scope. By the criterion already applied to Exercises
2.1–2.7 — adopt an exercise when the main text depends on it — both are adopted
here.

| Locator | Statement | Page | Roadmap article |
| --- | --- | --- | --- |
| Lem. 4.1 | Two morphisms `X → Y` of varieties agreeing on a nonempty open subset are equal | 24 | [Morphisms agreeing on an open set](../roadmap/rational-maps/morphism-agreement.md) |
| Def. | Rational map `φ : X ⇢ Y` as an equivalence class of pairs `⟨U, φ_U⟩`; dominant | 24 | [Rational maps](../roadmap/rational-maps/rational-map.md) |
| Infrastructure | Identity and composition for dominant rational maps; the category used in Theorem 4.4 | 24–26 | [Composition of dominant rational maps](../roadmap/rational-maps/rational-map-composition.md) |
| Def. | Birational map; birationally equivalent | 24 | [Birational maps](../roadmap/rational-maps/birational-map.md) |
| Lem. 4.2 | For a hypersurface `Y = Z(f)` in `𝔸ⁿ`, `𝔸ⁿ − Y` is isomorphic to `Z(x_{n+1} f − 1) ⊆ 𝔸ⁿ⁺¹`, hence affine with ring `k[x₁,…,x_n]_f` | 25 | [Localized coordinate ring](../roadmap/rational-maps/principal-open-coordinate-ring.md), [Complement of a hypersurface](../roadmap/rational-maps/hypersurface-complement.md) |
| Prop. 4.3 | On any variety the open affine subsets form a base for the topology | 25 | [Affine sets are a base](../roadmap/rational-maps/affine-base.md) |
| Thm. 4.4 | Dominant rational maps `X ⇢ Y` correspond bijectively to `k`-algebra homomorphisms `K(Y) → K(X)`; arrow-reversing equivalence with finitely generated field extensions of `k` | 25–26 | [Rational maps and function fields](../roadmap/rational-maps/rational-map-function-field.md) |
| Cor. 4.5 | `X`, `Y` birational ⟺ they have isomorphic open subsets ⟺ `K(X) ≅ K(Y)` | 26 | [Birational criterion](../roadmap/rational-maps/birational-criterion.md) |
| Thm. 4.6A | Theorem of the primitive element | 27 | [Separably generated extensions](../roadmap/rational-maps/separably-generated.md) |
| Def. | Separably generated extension; separating transcendence base | 27 | [Separably generated extensions](../roadmap/rational-maps/separably-generated.md) |
| Thm. 4.7A | A finitely generated separably generated extension has a separating transcendence base inside any generating set | 27 | [Separably generated extensions](../roadmap/rational-maps/separably-generated.md) |
| Thm. 4.8A | Over a perfect field every finitely generated field extension is separably generated | 27 | [Separably generated extensions](../roadmap/rational-maps/separably-generated.md) |
| Prop. 4.9 | Every variety of dimension `r` is birational to a hypersurface in `ℙ^{r+1}` | 27 | [Birational to a hypersurface](../roadmap/rational-maps/birational-hypersurface.md) |
| Constr. | Blowing up `𝔸ⁿ` at the origin; the blow-up of a closed subvariety; `φ : Ỹ → Y` is a birational morphism | 28–29 | [Blowing up](../roadmap/rational-maps/blowing-up.md) |
| Ex. 4.9.1 | Blowing up the plane cubic `y² = x²(x + 1)` at the origin separates its two branches | 29 | [Blowing up](../roadmap/rational-maps/blowing-up.md) |

Adopted from earlier sections because §4 depends on them:

| Locator | Statement | Page | Roadmap article |
| --- | --- | --- | --- |
| Ex. 2.9(a) | For `Y ⊆ 𝔸ⁿ` affine, the projective closure `Ȳ ⊆ ℙⁿ` has `I(Ȳ)` generated by the homogenisations `β(I(Y))` | 12 | [Projective closure](../roadmap/rational-maps/projective-closure.md) |
| Ex. 2.14 | The Segre embedding `ψ : ℙʳ × ℙˢ → ℙᴺ`, `N = rs + r + s`, has image the subvariety `Z(𝔞)` cut out by the kernel of `z_ij ↦ xᵢyⱼ` | 13 | [The Segre embedding](../roadmap/rational-maps/segre-embedding.md) |
| Ex. 3.16(a),(b) | `X × Y` is a quasi-projective variety, projective when `X` and `Y` are | 22 | [Products of varieties](../roadmap/rational-maps/product-variety.md) |

Ex. 3.16(c), that `X × Y` is a product in the category of varieties, is starred
in the source. Only what §4 uses is claimed: the two projections are morphisms
and a pair of morphisms into the factors induces one into the product.

## I.5

Nonsingular Varieties, approved span from the beginning of the section on
book p. 31 through Theorem 5.3 on p. 33. This is coverage unit
`chapter-i-section-5-geometry`. The completion material begins immediately
after Theorem 5.3 on the same printed page and is not part of this unit.

| Locator | Statement | Page | Roadmap article |
| --- | --- | --- | --- |
| Def. | For an affine variety `Y ⊆ 𝔸ⁿ` of dimension `r`, with `I(Y)` generated by `f₁,…,fₜ`, the point `P ∈ Y` is nonsingular when the matrix `((∂fᵢ/∂xⱼ)(P))` has rank `n − r`; `Y` is nonsingular when this holds at every point | 31 | [Nonsingular points of an affine variety](../roadmap/nonsingular-varieties/affine-nonsingular-points.md) |
| After Def. | The matrix `((∂fᵢ/∂xⱼ)(P))` is the Jacobian matrix at `P`; the condition is independent of the chosen generators of `I(Y)` | 32 | [Jacobian rank is independent of generators](../roadmap/nonsingular-varieties/jacobian-rank-invariance.md) |
| Def. | A Noetherian local ring `(A, 𝔪)` with residue field `κ = A/𝔪` is regular when `dim_κ 𝔪/𝔪² = dim A` | 32 | [Regular local rings](../roadmap/nonsingular-varieties/regular-local-rings.md) |
| Thm. 5.1 | For an affine variety `Y ⊆ 𝔸ⁿ` and `P ∈ Y`, the Jacobian definition says that `Y` is nonsingular at `P` if and only if the local ring `𝒪_{P,Y}` is a regular local ring | 32 | [The Jacobian criterion](../roadmap/nonsingular-varieties/jacobian-criterion.md) |
| Def. | An arbitrary variety `Y` is nonsingular at `P` when `𝒪_{P,Y}` is a regular local ring; `Y` is nonsingular when this holds at every point, and singular otherwise | 32 | [Intrinsic nonsingularity](../roadmap/nonsingular-varieties/intrinsic-nonsingularity.md) |
| Prop. 5.2A | If `(A, 𝔪)` is a Noetherian local ring with residue field `κ`, then `dim_κ 𝔪/𝔪² ≥ dim A` | 33 | [The cotangent-dimension bound](../roadmap/nonsingular-varieties/cotangent-dimension-bound.md) |
| Thm. 5.3 | For a variety `Y`, the set `Sing Y` of singular points is a proper closed subset of `Y` | 33 | [The singular locus is proper and closed](../roadmap/nonsingular-varieties/singular-locus.md) |

For Theorem 5.1, Hartshorne writes `𝔞_P` for the maximal ideal of the
ambient polynomial ring at `P`, identifies the cotangent quotient with
`𝔞_P/(I(Y) + 𝔞_P²)`, and obtains
`dim_k 𝔪/𝔪² + rank J = n`; Theorem 3.2(c) supplies
`dim 𝒪_{P,Y} = dim Y`. For Theorem 5.3, the affine singular locus is cut out
by `I(Y)` together with all `(n − r) × (n − r)` minors of the Jacobian.
Properness is reduced, using Proposition 4.9 and Corollary 4.5, to an affine
hypersurface `Z(f)`: if every partial derivative vanished, then in positive
characteristic `f` would be a `p`th power because `k` is algebraically closed,
contradicting irreducibility. Proposition 5.2A is one of Hartshorne's quoted
commutative-algebra results and is therefore background rather than a claim of
the book's proof.

## I.5 deferred completion and analytic material

This contiguous portion of the running text follows Theorem 5.3 on printed
p. 33 and ends before Theorem 5.7A on p. 35. It is deferred pending a separate
completion scope and is not included in coverage unit
`chapter-i-section-5-geometry`.

| Locator | Material | Pages | Disposition |
| --- | --- | --- | --- |
| After Thm. 5.3 | The `𝔪`-adic topology and completion `Â = lim← A/𝔪ⁿ` | 33 | Deferred pending a separate completion scope |
| Thm. 5.4A | Completion of a Noetherian local ring: local structure and injectivity; completion of a finite module as tensor product; preservation of dimension and regularity | 34 | Deferred background |
| Thm. 5.5A | A complete regular local ring of dimension `n` containing a field is isomorphic to `κ[[x₁,…,xₙ]]`, where `κ` is its residue field | 34 | Deferred background |
| Def.; Ex. 5.6.1–5.6.3 | Analytically isomorphic points; dimension invariance; nonsingular points of equal dimension; the plane nodal cubic is analytically isomorphic to the crossing `xy = 0`, showing that completion need not preserve being a domain | 34–35 | Deferred pending a separate completion scope |

## I.5 exercises and exercise-only prerequisite

Theorem 5.7A is in the running text on printed p. 35, but Hartshorne introduces
it only for Exercise 5.15. Neither that background result nor the exercises on
printed pp. 35–39 are part of the approved scope.

| Locator | Material | Pages | Disposition |
| --- | --- | --- | --- |
| Thm. 5.7A | Elimination theory for common nontrivial zeros of homogeneous polynomials with indeterminate coefficients | 35 | Out of scope; it is introduced only for Exercise 5.15 |
| Ex. 5.1–5.15 | Singularities, multiplicities, intersection multiplicity, blow-ups, projective Jacobians, tangent spaces, quadrics, normality, analytic singularities, and families of plane curves | 35–39 | Out of scope; the exercises were not adopted |

## Sections not decomposed

These are read and located but carry no roadmap articles. See the
[coverage contract](../coverage/README.md) for what that means.

| Section | Title | Pages |
| --- | --- | --- |
| I.6 | Nonsingular Curves | 39–47 |
| I.7 | Intersections in Projective Space | 47–55 |
| I.8 | What Is Algebraic Geometry? | 55–59 |
| II | Schemes | 60–200 |
| III | Cohomology | 201–259 |
| IV | Curves | 293–349 |
| V | Surfaces | 356–420 |

## Standing conventions

Hartshorne fixes an algebraically closed field `k` throughout Chapter I and
every statement above is read under that hypothesis. He also takes "variety" to
mean *irreducible*: the empty set is not irreducible, and an algebraic set that
decomposes is not a variety. Both conventions stay implicit in the source but
have to be written into every Lean statement, so articles state them rather than
inheriting them.
