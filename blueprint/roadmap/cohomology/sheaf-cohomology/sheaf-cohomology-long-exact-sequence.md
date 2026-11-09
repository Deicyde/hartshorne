---
article_id: af_acc41f7e6e3920d05b1ce349
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.sheafCohomologyδ Hartshorne.sheafCohomology_mono_map_f Hartshorne.sheafCohomology_exact₂ Hartshorne.sheafCohomology_exact₃ Hartshorne.sheafCohomology_exact₁ Hartshorne.sheafCohomologyδ_naturality
---

# The long exact sequence of sheaf cohomology

For every short exact sequence
$0\longrightarrow F'\longrightarrow F\longrightarrow F''\longrightarrow 0$
of abelian sheaves on a topological space $X$ there are connecting
homomorphisms $H^{n}(X,F'')\longrightarrow H^{n+1}(X,F')$ for $n\ge 0$,
natural in morphisms of short exact sequences, such that the sequence

$0\longrightarrow H^{0}(X,F')\longrightarrow H^{0}(X,F)\longrightarrow H^{0}(X,F'')\longrightarrow H^{1}(X,F')\longrightarrow\cdots$

is exact. This is the long exact sequence of right derived functors applied
to $\Gamma(X,-)$.

## Depends on

- [Sheaf cohomology](sheaf-cohomology.md)
- [The long exact sequence of right derived functors](../derived-functors/right-derived-long-exact-sequence.md)

## Sources

- [Hartshorne III.2, delegated long exact sequence, printed p. 207](../../../sources/hartshorne-iii-1-2.md#enough-injectives-and-cohomology-printed-pp-206208)
