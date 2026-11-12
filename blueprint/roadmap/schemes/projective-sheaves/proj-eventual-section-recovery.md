---
article_id: af_b8a5e47c59222d17169bdad2
declaration: theorem
origin: cited
lean: Hartshorne.EventualSectionRecovery.exists_bijective_alphaComponent Hartshorne.EventualSectionRecovery.alpha Hartshorne.EventualSectionRecovery.alphaComponent Hartshorne.EventualSectionRecovery.alpha_of_mem Hartshorne.EventualSectionRecovery.gammaStarMap Hartshorne.EventualSectionRecovery.gammaStarMap_alpha
statement: formalized
proof: formalized
---

# Eventual recovery from graded sections

Let $S_{0}=A$ be a finite-type algebra over a field, let $S$ be generated in
degree one with $S_{1}$ finite over $A$, and let $M$ be a finite graded
$S$-module. The natural graded map

$M\to\Gamma_*(\widetilde{M})$

is an isomorphism in every sufficiently large degree.

For homogeneous $m \in M_d$, its degree-$d$ component is the global section of
$\widetilde{M}(d)$ obtained from $m \in M(d)_0$ through the sheaf map
$M(d)_0\to\Gamma(\operatorname{Proj}S,\widetilde{M(d)})$ and the isomorphism
$\widetilde{M(d)}\cong\widetilde{M}(d)$. Construction and naturality of this graded map are included
as supporting data; the twist is essential because $\widetilde{M}$ need not have
a global section $m$ in every degree.

## Depends on

- [The graded global-sections module](graded-global-sections-module.md)
- [The sheaf of a graded module on Proj](proj-graded-module-sheaf.md)

## Proof depends on

- [Finiteness of projective global sections](projective-global-sections-finite.md)

## Sources

- [Hartshorne II.5, Exercise 5.9(a,b) (p.125)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
