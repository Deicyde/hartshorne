---
article_id: af_094f67cb8eec8e36da045be8
declaration: theorem
origin: cited
source_units: [chapter-ii-section-8]
---

# A nowhere-vanishing section of a high-rank generated bundle

Let `X` be an `n`-dimensional variety and let `E` be locally free of rank
strictly greater than `n`. If a finite-dimensional subspace
`V subset Gamma(X,E)` generates `E`, then some `s in V` is nonzero in every
fibre:

`s_x notin m_x E_x` for every `x in X`.

Consequently `s` induces an exact sequence

`0 -> O_X -> E -> E' -> 0`

with `E'` locally free.

## Depends on

- [Generation by global sections](../../schemes/projective-sheaves/globally-generated-module-sheaf.md)
- [The bad-hyperplane incidence correspondence](../../schemes/differentials/canonical-bertini/bertini-bad-hyperplane-incidence.md)

## Proof depends on

- The incidence of pairs `(x,s)` with `s(x)=0` has fibres in `V` of
  codimension `rank(E)>dim X`; its image has proper closure in `V`.
- Outside that image, the section is a unimodular element in every stalk;
  local bases containing it identify the cokernel as locally free.

## Sources

- [Hartshorne II.8, Exercise 8.2, p.187](../../../sources/hartshorne-ii-8.md#source-boundary-and-adoption-policy)
- [Hartshorne V.2, Exercise 2.3(a), pp.383–384](../../../sources/hartshorne-v-2.md#exercise-disposition-printed-pp383386)
