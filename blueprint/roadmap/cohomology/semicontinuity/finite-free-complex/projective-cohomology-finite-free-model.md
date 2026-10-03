---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# A finite-free model for projective cohomology

Under the fixed hypotheses `A` Noetherian, `Y = Spec A`, `f : X -> Y`
projective, and `F` coherent and flat over `Y`, there is a bounded-above
complex `L` of finitely generated free `A`-modules with natural isomorphisms

`H^i(L tensor_A M) ~= H^i(X, F tensor_A M)`

for every `A`-module `M` and every `i >= 0`. These isomorphisms commute with
the connecting morphisms and therefore identify the two delta functors.

## Depends on

- [Cohomology after tensor is a delta functor](cohomology-tensor-delta-functors.md)
- [Replacing a bounded-above complex by finite free modules](finite-free-complex-replacement.md)
- [Affine covers compute sheaf cohomology](../../cech-cohomology/affine-cover-comparison.md)
- [Coherent projective cohomology is finite](../../projective-cohomology/projective-coherent-cohomology-finite.md)

## Proof depends on

- For a finite affine cover of `X`, the Cech complex of `F` is bounded, its
  terms are flat over `A`, and tensoring it with `M` gives the Cech complex of
  `F tensor_A M`.

## Sources

- [Hartshorne III.12, Proposition 12.2, pp.282–283](../../../../sources/hartshorne-iii-11-12.md#cohomology-after-tensor-and-finite-free-models-pp281287)
- [Stacks Project, perfect derived global sections, tag 07VK](../../../../sources/hartshorne-iii-11-12.md#cohomology-after-tensor-and-finite-free-models-pp281287)
