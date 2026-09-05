# The rings of a projective variety

Theorem 3.2 computes the three rings of an affine variety and finds that the
coordinate ring loses nothing. Theorem 3.4 does the same for a projective
variety and finds the opposite: the global regular functions see nothing at all,
`𝒪(Y) = k`, and everything local lives in graded localisations of `S(Y)`.

The three parts need different equipment, which is why they are separate nodes.
Part (c) is proved; part (b) is reduced to the affine case with one graded step
outstanding; part (a) is untouched.

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

## Ingredients

- [The charts are isomorphisms of varieties](chart-isomorphism.md)
- [Graded localization](graded-localization.md)

## Theorem 3.4

- [The global regular functions of a projective variety](projective-global-regular.md)
- [The local ring of a projective variety](projective-local-ring.md)
- [The function field of a projective variety](projective-function-field.md)
