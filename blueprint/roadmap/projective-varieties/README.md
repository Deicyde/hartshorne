# Projective varieties

Hartshorne rebuilds §1 over projective `n`-space, and the point of the exercise
is that almost nothing changes. Homogeneous polynomials are not functions on
`ℙⁿ`, but their vanishing is well defined, so `Z` and `J` still make sense and
still form the same order-reversing pair. The grading is the only new ingredient,
and it costs exactly one wrinkle: the irrelevant ideal `S₊ = ⨁_{d>0} S_d` cuts
out the empty set, so it has to be excluded from the correspondence by hand.

The section's real content is Proposition 2.2, which says `ℙⁿ` is covered by
`n + 1` copies of `𝔸ⁿ`, glued along the standard charts `φᵢ`. That is what makes
projective geometry locally affine, and it is the mechanism by which §3 computes
the local rings and function field of a projective variety from the affine case
it already knows. Everything in Chapter I after this point uses it.

A note on where the mathematics lives: Hartshorne states only 2.1, 2.2 and 2.3
in the running text and leaves the homogeneous Nullstellensatz, the ideal
correspondence, and both dimension computations to Exercises 2.1–2.7. Those
results are used later in the book, so this chapter formalizes them as source
targets rather than skipping them.

## The projective dictionary

- [Projective space](projective-space.md)
- [Homogeneous ideals](homogeneous-ideal.md)
- [Projective algebraic sets](projective-algebraic-set.md)
- [The Zariski topology on projective space](projective-zariski-topology.md)
- [The homogeneous vanishing ideal](homogeneous-vanishing-ideal.md)
- [The homogeneous Nullstellensatz](projective-nullstellensatz.md)
- [Algebraic sets and homogeneous radical ideals](homogeneous-ideal-correspondence.md)
- [Projective and quasi-projective varieties](projective-variety.md)

## Projective space is locally affine

- [The standard affine charts](standard-affine-charts.md)
- [Varieties are covered by affine pieces](affine-cover.md)
- [Projective space is a Noetherian space](projective-space-noetherian.md)

## Dimension

- [Dimension of the homogeneous coordinate ring](homogeneous-coordinate-ring-dimension.md)
- [Dimension in projective space](projective-dimension.md)
