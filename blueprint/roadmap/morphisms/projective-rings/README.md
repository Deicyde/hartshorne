# The rings of a projective variety

Theorem 3.2 computes the three rings of an affine variety and finds that the
coordinate ring loses nothing. Theorem 3.4 does the same for a projective
variety and finds the opposite: the global regular functions see nothing at all,
`𝒪(Y) = k`, and everything local lives in graded localisations of `S(Y)`.

All three parts are proved. They need different equipment, which is why they
are separate nodes: (b) and (c) reduce to the affine case one chart at a time,
while (a) has no affine analogue and must hold every chart in view at once.

Parts (b) and (c) reduce to the affine case, one chart at a time. That reduction
is not the one-line remark it looks like: the chart has to be an isomorphism of
varieties and not merely a homeomorphism, and the local ring and function field
have to be transported along it, which needs them to exist over an abstract
variety in the first place. Graded localisation is what the affine answers get
rewritten into.

Part (a) has no affine analogue. Its integrality argument needs the whole affine
cover at once rather than one chart at a time, and it is the structural reason
projective varieties need sheaf cohomology rather than global functions — the
motivation Hartshorne gives for Chapters II and III.

Formalising it turned up the one place where his notation genuinely hides
something: treating `K(Y)` and `S(Y)_((0))` as the same field makes the
identification invisible, but it has to be built, and if it is built chart by
chart then readings on different charts are not comparable. The way out was to
keep the chart readings pointwise, where there is nothing to identify.

## Ingredients

- [The charts are isomorphisms of varieties](chart-isomorphism.md)
- [Graded localization](graded-localization.md)
- [The homogeneous prime at a point](point-ideal.md)
- [An element stabilising a finite-dimensional subspace is integral](stable-subspace.md)
- [Reading a global regular function on a chart](chart-reading.md)
- [The degree bound](degree-bound.md)

## Theorem 3.4

- [The global regular functions of a projective variety](projective-global-regular.md)
- [The local ring of a projective variety](projective-local-ring.md)
- [The function field of a projective variety](projective-function-field.md)
