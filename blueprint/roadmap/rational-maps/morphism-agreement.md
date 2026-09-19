---
article_id: af_daad9faeda5a941ac86e9d79
declaration: theorem
origin: cited
source_units: [chapter-i-section-4]
statement: formalized
proof: formalized
lean: Hartshorne.eq_of_eqOn_isOpen_hom
---

# Morphisms agreeing on an open set

Let `X` and `Y` be varieties and `φ, ψ : X → Y` morphisms. If there is a
nonempty open `U ⊆ X` with `φ|_U = ψ|_U`, then `φ = ψ` (Lemma 4.1).

This is the whole reason rational maps are well behaved, and it is the algebraic
substitute for the Hausdorff separation that would make the statement trivial in
topology. The Zariski topology is not Hausdorff and the statement is not
topologically formal: it is the assertion that the diagonal of `Y × Y` is
closed.

## Hartshorne's proof, and the proof used here

Hartshorne reduces to `Y = ℙⁿ`, gives `ℙⁿ × ℙⁿ` its Segre structure, observes
that the diagonal `Δ` is cut out by the equations `xᵢyⱼ = xⱼyᵢ` and so is
closed, and concludes because `(φ × ψ)(U) ⊆ Δ` with `U` dense.

That route makes products a prerequisite of everything downstream, and products
are themselves an adopted exercise. The same equations prove the lemma without
constructing the product, by reading them chartwise, and that is the route used
here:

- the agreement locus `Z = {x ∈ X : φ(x) = ψ(x)}` is closed;
- it contains `U`, which is dense because `X` is irreducible;
- so `Z = X`.

Only the first clause has content. Cover `X` by the open sets
`W_{ij} = φ⁻¹(Uᵢ) ∩ ψ⁻¹(Uⱼ)`, which do cover since the charts cover `ℙⁿ`. On
`W_{ij}` write `a₀,…,aₙ` for the homogeneous coordinates of `φ` normalised by
`aᵢ = 1` and `b₀,…,bₙ` for those of `ψ` normalised by `bⱼ = 1`; each is a
regular function on `W_{ij}`, being a chart coordinate of a morphism. Two points
of `ℙⁿ` given by nonzero coordinate vectors are equal exactly when all the
`2 × 2` minors vanish, so

`Z ∩ W_{ij} = {x ∈ W_{ij} : a_l(x) b_m(x) − a_m(x) b_l(x) = 0 for all l, m}`,

a common zero set of regular functions, hence closed in `W_{ij}`. Closedness is
local, so `Z` is closed.

The mathematics is Hartshorne's — these are the Segre equations for the
diagonal — but arranged so that the Segre embedding is needed only where the
source needs it for its own sake, in the blow-up construction.

## Status

Proved, as `Hartshorne.eq_of_eqOn_isOpen_hom`, by the route above.

The target is `Variety.ofQuasiProjective hY` rather than an arbitrary
`Variety`, and that restriction is forced rather than convenient: the abstract
structure imposes no separation axiom, and the line with a doubled origin
satisfies it while failing the lemma. Hartshorne's varieties are the four
concrete kinds, all quasi-projective, so nothing in the source is lost.

Two small pieces carry the argument. `eq_of_minors_eq_zero` says a vanishing
family of minors forces two points of `ℙⁿ` to agree, which is where the scalar
relating the two coordinate vectors is written down. And `div_minor_eq_zero_iff`
says the minor normalised by the two chart denominators vanishes exactly when
the minor does — that is the step that turns an expression in homogeneous
coordinates, which is not a function on `ℙⁿ`, into a difference of products of
chart coordinates, which is.

## Depends on

- [Morphisms](../morphisms/morphism.md)
- [Varieties](../morphisms/variety.md)
- [Regular functions on a quasi-projective variety](../morphisms/regular-function-quasi-projective.md)

## Proof depends on

- [The standard affine charts](../projective-varieties/standard-affine-charts.md)
- [Regular functions are continuous](../morphisms/regular-function-continuous.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)

## Sources

- [Hartshorne I.4, Lemma 4.1 (p. 24)](../../sources/hartshorne.md#i4)
