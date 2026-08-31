# Hartshorne, *Algebraic Geometry*

Robin Hartshorne, *Algebraic Geometry*, Springer, Graduate Texts in Mathematics
52, 1977. ISBN 978-1-4757-3849-0.

The book is not redistributed with this repository. Locators below are **printed
book page numbers**, which is the numbering the text itself uses in cross
references. If you are reading a scan whose front matter is included, the
1977 Springer printing has `pdf page index = book page + 14`, so book page 1
(the first page of Chapter I) is the fifteenth page of the file.

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
| Thm. 1.8A | For a f.g. `k`-algebra domain `B`: `dim B = trdeg_k K(B)`, and `height 𝔭 + dim B/𝔭 = dim B` | 6 | [Dimension of a finitely generated domain](../roadmap/affine-varieties/dim-fg-domain.md) |
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
| Ex. 2.2 | `Z(𝔞) = ∅` iff `√𝔞` is `S` or `S₊`, iff `𝔞 ⊇ S_d` for some `d > 0` | 11 | [Projective Nullstellensatz](../roadmap/projective-varieties/projective-nullstellensatz.md) |
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
| Thm. 3.2 | For `Y` affine: `𝒪(Y) ≅ A(Y)`; points ↔ maximal ideals; `𝒪_P ≅ A(Y)_{𝔪_P}` with `dim 𝒪_P = dim Y`; `K(Y) ≅ Frac A(Y)` of transcendence degree `dim Y` | 17 | [Rings of an affine variety](../roadmap/morphisms/affine-variety-rings.md) |
| Prop. 3.3 | `φᵢ : Uᵢ → 𝔸ⁿ` is an isomorphism of varieties | 18 | [Charts are isomorphisms](../roadmap/morphisms/chart-isomorphism.md) |
| Def. | Graded localizations `S_(𝔭)` and `S_(f)` | 18 | [Graded localization](../roadmap/morphisms/graded-localization.md) |
| Thm. 3.4 | For `Y` projective: `𝒪(Y) = k`; `𝒪_P = S(Y)_(𝔪_P)`; `K(Y) ≅ S(Y)_((0))` | 18–19 | [Rings of a projective variety](../roadmap/morphisms/projective-variety-rings.md) |
| Prop. 3.5 | `Hom(X, Y) ≅ Hom_{k-alg}(A(Y), 𝒪(X))` for `Y` affine, `X` any variety | 19 | [Morphisms into an affine variety](../roadmap/morphisms/hom-affine-bijection.md) |
| Lem. 3.6 | `ψ : X → Y ⊆ 𝔸ⁿ` is a morphism iff each `xᵢ ∘ ψ` is regular | 20 | [Criterion for a morphism to an affine variety](../roadmap/morphisms/morphism-to-affine-criterion.md) |
| Cor. 3.7 | Affine varieties `X`, `Y` are isomorphic iff `A(X) ≅ A(Y)` as `k`-algebras | 20 | [Isomorphism via coordinate rings](../roadmap/morphisms/affine-iso-iff-algebra-iso.md) |
| Cor. 3.8 | `X ↦ A(X)` is an arrow-reversing equivalence between affine varieties over `k` and finitely generated integral domains over `k` | 20 | [Equivalence with finitely generated domains](../roadmap/morphisms/affine-variety-equivalence.md) |
| Thm. 3.9A | Finiteness of integral closure | 20 | **No article.** Hartshorne states it in §3 with "we include here an algebraic result which will be used in the exercises"; nothing in the main text of §§1–3 uses it, and the exercises that do are out of scope. It is needed from §6 onward. |

## Sections not decomposed

These are read and located but carry no roadmap articles. See the
[coverage contract](../coverage/README.md) for what that means.

| Section | Title | Pages |
| --- | --- | --- |
| I.4 | Rational Maps | 24–31 |
| I.5 | Nonsingular Varieties | 31–39 |
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
