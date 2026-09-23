# Hartshorne, *Algebraic Geometry*

Robin Hartshorne, *Algebraic Geometry*, Springer, Graduate Texts in Mathematics
52, 1977. ISBN 978-1-4757-3849-0.

The book is not redistributed with this repository. Locators below are **printed
book page numbers**, which is the numbering the text itself uses in cross
references. If you are reading a scan whose front matter is included, the
1977 Springer printing has `pdf page index = book page + 15`, so book page 1
(the first page of Chapter I) is the sixteenth page of the file. Checked
against book pages 12, 13, 20, 22–24, 27, 30, and 39–45.

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
| Thm. 3.9A | If `A` is a finitely generated `k`-algebra domain with fraction field `K` and `L/K` is finite algebraic, then the integral closure of `A` in `L` is finite over `A` and finitely generated over `k` | 20 | [Frobenius finiteness](../roadmap/curve-normalization/frobenius-finite-affine-algebra.md), [purely inseparable normalization](../roadmap/curve-normalization/purely-inseparable-normalization-finite.md), [polynomial normalization](../roadmap/curve-normalization/polynomial-normalization-finite.md), and [finiteness of integral closure](../roadmap/curve-normalization/finite-integral-closure.md) |

Hartshorne cites Zariski–Samuel, vol. I, Chapter V, Theorem 9 for Theorem
3.9A. [Stacks Project, Tag 0335](https://stacks.math.columbia.edu/tag/0335)
gives a modern route through the fact that finite-type algebras over fields are
Nagata. The pinned Mathlib theorem proves the finite-normalization conclusion
only over an integrally closed base and for a separable extension, so it is not
an exact match.

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

Additional exercises adopted under the main-text dependency rule:

| Locator | Statement | Page | Roadmap article |
| --- | --- | --- | --- |
| Ex. 2.9(a) | For `Y ⊆ 𝔸ⁿ` affine, the projective closure `Ȳ ⊆ ℙⁿ` has `I(Ȳ)` generated by the homogenisations `β(I(Y))` | 12 | [Projective closure](../roadmap/rational-maps/projective-closure.md) |
| Ex. 2.14 | The Segre embedding `ψ : ℙʳ × ℙˢ → ℙᴺ`, `N = rs + r + s`, has image the subvariety `Z(𝔞)` cut out by the kernel of `z_ij ↦ xᵢyⱼ` | 13 | [The Segre embedding](../roadmap/rational-maps/segre-embedding.md) |
| Ex. 3.16(a),(b) | `X × Y` is a quasi-projective variety, projective when `X` and `Y` are | 22 | [Products of varieties](../roadmap/rational-maps/product-variety.md) |
| Ex. 4.8(a), needed consequence | A positive-dimensional quasi-projective variety has infinitely many points | 30 | [Quasi-projective curves have the cofinite topology](../roadmap/curve-normalization/quasiprojective-curve-cofinite.md) |

Ex. 3.16(c), that `X × Y` is a product in the category of varieties, is starred
in the source. Only what §4 uses is claimed: the two projections are morphisms
and a pair of morphisms into the factors induces one into the product.
Exercise 4.8(a) enters only because the discussion before Proposition 6.7 uses
its infinitude consequence; its stronger cardinality statement and part (b)
remain outside the roadmap.

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

## I.6 valuation and DVR background

Nonsingular Curves, first completed block on printed pp. 39–41 through Lemma
6.4. Hartshorne first recalls valuation and Dedekind-domain facts, then
identifies the local ring of a nonsingular curve point as a discrete valuation
ring inside the function field. The quoted Theorem 6.3A is deliberately split
into its own unit: it occurs before Lemma 6.4 in the text but is first used in
Hartshorne's proof of Lemma 6.5.

| Locator | Statement | Page | Roadmap article |
| --- | --- | --- | --- |
| Intro.; Def. | A function field of dimension one over `k`; valuations, valuation rings, and valuation rings of `K/k` | 39–40 | [Curves](../roadmap/nonsingular-curves/curve.md), [Valuation rings are maximal local subrings](../roadmap/nonsingular-curves/valuation-ring-maximal-local-subring.md) |
| Def. | A local ring `B` contained in a field dominates `A` when `A ⊆ B` and `𝔪_B ∩ A = 𝔪_A` | 40 | [Valuation rings are maximal local subrings](../roadmap/nonsingular-curves/valuation-ring-maximal-local-subring.md) |
| Thm. 6.1A, first clause | A local subring of a field is a valuation ring iff it is maximal for domination | 40 | [Valuation rings are maximal local subrings](../roadmap/nonsingular-curves/valuation-ring-maximal-local-subring.md) |
| Thm. 6.1A, second clause | Every local subring of a field is dominated by a valuation ring | 40 | [Every local subring is dominated by a valuation ring](../roadmap/nonsingular-curves/valuation-ring-dominates-local-subring.md) |
| Def.; Thm. 6.2A | For a Noetherian local domain of dimension one, being a DVR, integrally closed, regular local, and having principal maximal ideal are equivalent | 40 | [Characterizations of discrete valuation rings](../roadmap/nonsingular-curves/dvr-characterizations.md) |
| Def.; after Thm. 6.2A | A Dedekind domain is an integrally closed Noetherian domain of dimension one; its localization at a nonzero prime is a DVR | 40 | [Localizations of a Dedekind domain are DVRs](../roadmap/nonsingular-curves/dedekind-localization-dvr.md) |

## I.6 integral-closure theorem

| Locator | Statement | Page | Roadmap article |
| --- | --- | --- | --- |
| Thm. 6.3A | The integral closure of a Dedekind domain in a finite extension of its fraction field is again a Dedekind domain, with no separability hypothesis | 40 | [Finite-length quotients](../roadmap/curve-normalization/krull-akizuki-quotient-finite.md), [Krull–Akizuki](../roadmap/curve-normalization/krull-akizuki.md), and [integral closures of Dedekind domains](../roadmap/curve-normalization/dedekind-integral-closure.md) |

The source cites Zariski–Samuel, vol. I, Chapter V, Theorem 19. The
[Krull–Akizuki theorem in Stacks Project, Tag 00PG](https://stacks.math.columbia.edu/tag/00PG)
is a modern proof source for the missing Noetherian step. The pinned Mathlib
theorem assumes separability. Open Mathlib PR
[#41755](https://github.com/leanprover-community/mathlib4/pull/41755) contains
the missing nonseparable Krull–Akizuki core, but is prior art rather than a
dependency of this roadmap.

## I.6 local structure and point separation

The paragraph after Theorem 6.3A uses Theorems 5.1 and 6.2A to put the local
ring of a nonsingular curve point inside its function field as a DVR. Lemma 6.4
then proves that the resulting local subring determines the point. Hartshorne's
proof places two points in a common affine chart. The Lean proof uses
the equivalent projective argument directly: a homogeneous linear fraction is
regular at one point and not the other. This avoids adding a general coordinate-
change API solely for this lemma while preserving its full quasi-projective
statement.

| Locator | Statement | Page | Roadmap article |
| --- | --- | --- | --- |
| After Thm. 6.3A | If `P` lies on a nonsingular curve `Y`, then `𝒪_{P,Y}` is a DVR whose fraction field is `K(Y)`, hence a valuation ring of `K(Y)/k` | 41 | [The function field is the fraction field of every local ring](../roadmap/nonsingular-curves/local-ring-fraction-field.md), [Dimension of the local ring of a variety](../roadmap/nonsingular-curves/local-ring-dimension.md), [Local rings of nonsingular curves are DVRs](../roadmap/nonsingular-curves/nonsingular-curve-local-ring-dvr.md), [Nonsingular curve points define discrete valuations](../roadmap/nonsingular-curves/nonsingular-curve-valuation.md) |
| Lem. 6.4 | If `Y` is quasi-projective, `P,Q ∈ Y`, and `𝒪_{Q,Y} ⊆ 𝒪_{P,Y}` inside `K(Y)`, then `P = Q` | 41 | [Linear fractions separate projective points](../roadmap/nonsingular-curves/projective-linear-separation.md), [Membership of a homogeneous fraction in a local ring](../roadmap/nonsingular-curves/homogeneous-fraction-local-membership.md), [The local ring determines the point](../roadmap/nonsingular-curves/local-ring-inclusion-determines-point.md) |

## I.6 normalization and finite poles

For a one-dimensional function field `K/k`, Hartshorne writes `C_K` for the
set of discrete valuation rings of `K/k`. His proof of Lemma 6.5 normalizes
`k[y]` for `y = x⁻¹` and invokes Theorems 3.9A and 6.3A. The Lean roadmap also
formalizes those exact background results, but its geometric branch uses an
equivalent two-chart argument: choose one separating parameter `t`, normalize
`k[t]` and `k[t⁻¹]` by the pinned separable integral-closure theorems, and use
the fact that every valuation ring contains `t` or `t⁻¹`. This keeps Lemma 6.5
and Corollary 6.6 available independently of the harder nonseparable branch.

| Locator | Statement | Pages | Roadmap article |
| --- | --- | --- | --- |
| Def. | `C_K` is the set of discrete valuation rings of `K/k`; poles and zeros are nonmembership and maximal-ideal membership | 39–42 | [Discrete valuation rings of a function field](../roadmap/curve-normalization/function-field-dvrs.md) |
| Proof infrastructure | A one-dimensional function field has a separating parameter; the normalizations of its two polynomial charts are finite-type Dedekind domains covering `C_K` | 41–42 | [Separating parameters](../roadmap/curve-normalization/separating-parameter.md), [two separable normalization charts](../roadmap/curve-normalization/separable-normalization-charts.md) |
| Proof infrastructure | A function-field DVR containing a Dedekind model is its localization at a unique center; finite-type Dedekind domains and their localizations have nonsingular affine curve models | 41–42 | [Centers and localizations](../roadmap/curve-normalization/dedekind-subring-localization.md), [Dedekind affine models](../roadmap/curve-normalization/dedekind-affine-model.md) |
| Lem. 6.5 | For `x ∈ K`, the set `{R ∈ C_K | x ∉ R}` is finite | 41 | [A rational function has finitely many poles](../roadmap/curve-normalization/finite-poles.md) |
| Cor. 6.6 | Every DVR of `K/k` is isomorphic to the local ring of a point on a nonsingular affine curve; the roadmap additionally preserves the compatible embeddings into `K` needed by Proposition 6.7 | 42 | [Every function-field DVR has a nonsingular affine model](../roadmap/curve-normalization/dvr-affine-model.md) |

## I.6 abstract nonsingular curves

Give `C_K` the cofinite topology. For an open `U`, Hartshorne defines
`𝒪(U) = ⋂_{R ∈ U} R` inside `K`; the residue-field identification supplied by
Corollary 6.6 reads each element as a `k`-valued function. Lemma 6.5 makes this
evaluation injective and makes every element of `K` regular on some nonempty
open subset. An abstract nonsingular curve is a nonempty open subset of `C_K`
with this regular-function structure.

The text uses the infinitude consequence of Exercise 4.8(a) here. Following
the project's exercise policy, the roadmap adopts only that consequence, not
the exercise's stronger cardinality equality or part (b).

| Locator | Statement | Pages | Roadmap article |
| --- | --- | --- | --- |
| Ex. 4.8(a), used here | A positive-dimensional variety is infinite; a quasi-projective curve has the cofinite topology | 30, 42 | [Quasi-projective curves have the cofinite topology](../roadmap/curve-normalization/quasiprojective-curve-cofinite.md) |
| Def.; discussion | The cofinite topology on `C_K`, the residue evaluation to `k`, regular functions on its opens, and the abstract nonsingular curve attached to a nonempty open | 42 | [Valuation-space topology](../roadmap/curve-normalization/valuation-space-topology.md), [residue fields](../roadmap/curve-normalization/valuation-residue-field.md), [regular functions](../roadmap/curve-normalization/valuation-regular-functions.md), [regularity axioms](../roadmap/curve-normalization/valuation-regular-functions-local.md), [abstract nonsingular curves](../roadmap/curve-normalization/abstract-nonsingular-curve.md), [their function fields](../roadmap/curve-normalization/valuation-space-function-field.md) |
| Prop. 6.7, affine input | A nonsingular affine curve has a Dedekind coordinate ring | 42–43 | [Nonsingular affine curves have Dedekind coordinate rings](../roadmap/curve-normalization/nonsingular-affine-curve-dedekind.md) |
| Prop. 6.7 | For a nonsingular quasi-projective curve `Y`, the map `P ↦ 𝒪_{P,Y}` identifies `Y` with an open abstract nonsingular subcurve of `C_{K(Y)}` | 42–43 | [The local-ring map has open image](../roadmap/curve-normalization/curve-local-ring-map-open.md), [nonsingular curves are open subcurves of their valuation spaces](../roadmap/curve-normalization/curve-to-valuation-space-iso.md) |

## I.6 deferred projective models

Proposition 6.8 begins the separate extension and projective-model milestone
leading to the unique nonsingular projective model of a one-dimensional
function field.

| Locator | Material | Pages | Disposition |
| --- | --- | --- | --- |
| Prop. 6.8 | A morphism from a punctured abstract nonsingular curve to a projective variety extends uniquely | 43–44 | Deferred to the projective-model milestone |
| Thm. 6.9; Cor. 6.10–6.12 | Existence and uniqueness of the nonsingular projective model and the equivalence with one-dimensional function fields | 44–45 | Deferred to the projective-model milestone |

## I.6 exercises

| Locator | Material | Pages | Disposition |
| --- | --- | --- | --- |
| Ex. 6.1–6.7 | Valuations, birational invariants, maps of curves, genus-zero and plane-curve applications | 46–47 | Out of scope; none is used through Proposition 6.7 |

## Sections not decomposed

These are read and located but carry no roadmap articles. See the
[coverage contract](../coverage/README.md) for what that means.

| Section | Title | Pages |
| --- | --- | --- |
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
