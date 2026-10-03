# Hartshorne II.1: Sheaves

Robin Hartshorne, *Algebraic Geometry*, Chapter II, §1. The mathematical
running text is printed pp. 61–65. Printed p. 60 is chapter and section
motivation. In the repository scan, printed page `n` is PDF zero-based index
`n + 14`, so the running text occupies indices 75–79.

This note records the statements used by the roadmap. It does not treat every
exercise as a formalization target. An exercise is adopted when approved
running text cites it, delegates a result to it, or later uses it.

## Boundary and representation

The stated pp. 60/61–68 boundary contains the running text and Exercises
1.1–1.21 only through the beginning of Exercise 1.21. Exercise 1.22 is on
printed p. 69 (PDF index 83), before §2 begins later on that page. It is adopted
as a deliberate one-item boundary expansion because Hartshorne explicitly uses
it to glue sheaves on p. 86 and recalls it again on p. 88.

Hartshorne requires a presheaf of abelian groups to have zero sections on the
empty open. Mathlib uses the broader modern convention that a presheaf is any
functor from opens opposite. The roadmap adopts Mathlib's convention and
records the source condition at the sheaf level, where
`TopCat.Sheaf.isTerminalOfEmpty` gives the zero group. No parallel project
wrapper for presheaves should be introduced.

Hartshorne's constant sheaf is presented concretely as continuous maps into a
discrete group. Mathlib has both an abstract sheafification-based constant
sheaf and a sheaf of continuous maps, but the pinned checkout does not contain
the source-shaped additive comparison. That bridge remains project work.

The project already has `Hartshorne.Variety.regular` and
`Hartshorne.Variety.LocalRingAt`. The regular-functions sheaf must reuse the
former, and its stalk comparison must identify the categorical stalk with the
existing quotient-of-germs local ring rather than define a second local ring.

## Presheaves and sheaves, printed p. 61

A presheaf of abelian groups assigns a group `F(U)` to each open `U` and a
restriction homomorphism to each inclusion, with identity and composition
laws. A sheaf is a presheaf satisfying locality and unique gluing for every
open cover. Morphisms are compatible families of homomorphisms on sections;
for Mathlib these are natural transformations.

## Basic examples, printed p. 62

Example 1.0.1 says that regular functions on open subsets of a variety form a
sheaf of rings. Its stalk at a point is the Chapter I local ring. The sheaf is
used in the comparison of varieties with schemes on printed p. 78.

Example 1.0.2 lists continuous real-valued, differentiable, and holomorphic
functions as analogous sheaves. These illustrations are not used by Chapter II
running text and are outside this roadmap.

Example 1.0.3 defines the constant sheaf associated to an abelian group `A` as
continuous maps into `A` with the discrete topology. On a connected nonempty
open its sections identify with `A`; when connected components are open, its
sections are a product of copies of `A`, one per component. Constant sheaves
are used later on printed pp. 112, 141, 145, and 167.

## Stalks, germs, and morphisms, printed pp. 62–63

The stalk `F_P` is the direct limit over open neighbourhoods of `P`. Its
elements are germs of sections, and a morphism induces a map on every stalk.

Proposition 1.1 states that a morphism of sheaves is an isomorphism if and only
if every induced stalk map is an isomorphism. Hartshorne proves injectivity by
local equality and surjectivity by choosing local lifts and gluing them.

## Associated sheaves, printed p. 64

Proposition–Definition 1.2 constructs `F⁺` from functions into the disjoint
union of stalks which are locally germs. The canonical map `F → F⁺` is initial
among maps from `F` to sheaves, determining `F⁺` uniquely up to unique
isomorphism. It induces isomorphisms on stalks, and is an isomorphism when `F`
is already a sheaf.

## Kernels, images, quotients, and exactness, printed pp. 63–65

Presheaf kernels, cokernels, and images are computed on every open. The
presheaf kernel of a sheaf morphism is a sheaf. The sheaf image and cokernel
are obtained by sheafifying the corresponding presheaves; the image embeds as
a subsheaf. A quotient sheaf is the sheafification of the pointwise quotient,
and its stalk is the quotient of stalks. Injective, surjective, and exact
morphisms are defined using these operations.

Caution 1.2.1 records that injectivity is sectionwise, while surjectivity is
not generally sectionwise. Surjectivity and exactness are instead detected on
stalks. The existence of a counterexample on global sections, requested in
Exercise 1.3(b), is not a target; only the local lifting criterion used later
is adopted.

## Sheaf functors, printed p. 65

For a continuous `f : X → Y`, direct image is
`(f_*F)(V) = F(f⁻¹(V))`. Inverse image is the associated sheaf of the
presheaf colimit over opens of `Y` containing `f(U)`. For an inclusion of a
subspace, inverse image is restriction, and its stalk at a point is the
original stalk.

## Adopted exercises and later-use evidence

| Exercise | Adopted statement | Printed page | Later Chapter II running-text use |
| --- | --- | --- | --- |
| 1.2(a–c) | Stalks commute with kernels and images; mono, epi, and exactness are stalkwise | 66 | Caution 1.2.1, p. 65; exactness of `M ↦ M~`, p. 111 |
| 1.3(a) | An epimorphism is locally liftable on an open cover | 66 | Proposition 5.6 proof, p. 113 |
| 1.4(a,b) | Sheafification preserves sectionwise injections; the image embeds as a subsheaf | 66 | Definition of image, p. 64 |
| 1.8 | Sections over an open form a left-exact functor | 66 | Proposition 5.6 proof, p. 113 |
| 1.9 | Direct sums of sheaves and their biproduct property | 66 | Operations on sheaves of modules, p. 109 |
| 1.10 | Direct limits are sheafified pointwise direct limits | 66–67 | Operations on sheaves of modules, p. 109 |
| 1.12 | Inverse limits are pointwise inverse limits | 67 | Operations on sheaves of modules, p. 109; reproved as Proposition 9.2, pp. 192–193 |
| 1.14 | Support of a section and of a sheaf; section support is closed | 67 | Support of `O_X/F` in Proposition 5.9, p. 116 |
| 1.15 | `U ↦ Hom(F|U,G|U)` is a sheaf | 67 | Sheaf Hom for modules, p. 109 |
| 1.18 | `f⁻¹` is left adjoint to `f_*` | 68 | Inverse images of modules, pp. 109–110 |
| 1.19(a,b) | Closed and open extension by zero and their stalks | 68 | Example 5.2.3, p. 111; formal schemes, p. 196 |
| 1.22 | Compatible sheaves on an open cover glue uniquely | 69 | Reduced induced subschemes, p. 86; gluing morphisms, p. 88 |

## Excluded and deferred exercises

Exercises 1.1, 1.3(b), 1.5–1.7, 1.11, 1.13, 1.17, 1.19(c), and
1.21 are outside this Chapter II running-text slice. Their conclusions are
either unused here, already subsumed by Mathlib's categorical API, or examples
requested only inside the exercise set.

Exercises 1.16 (flasque sheaves) and 1.20 (sections with supports) are deferred
to the Chapter III cohomology milestones. Exercise 1.14 is adopted only to the
extent stated above; a separate example showing that a sheaf's support need
not be closed is not required here.

## Pinned Mathlib audit

The audited checkout is Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`
(`v4.33.1`). Exact matches are recorded on the corresponding roadmap leaves.
The principal files are `Mathlib/Topology/Sheaves/Presheaf.lean`,
`Sheaf.lean`, `Stalks.lean`, `Sheafify.lean`, `Functors.lean`,
`Limits.lean`, `Abelian.lean`, `AddCommGrpCat.lean`, and
`LocallySurjective.lean`, together with
`Mathlib/CategoryTheory/Sites/Sheafification.lean` and `Limits.lean`.

Focused searches found only partial infrastructure, not exact source-shaped
results, for the additive constant-sheaf model, generic supports, additive
sheaf Hom, extension by zero, restriction-stalk packaging, and gluing sheaves
on a fixed space. Targeted read-only GitHub PR searches for these gaps
returned no matching pull requests.
