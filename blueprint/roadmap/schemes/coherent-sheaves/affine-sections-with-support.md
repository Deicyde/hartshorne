---
article_id: af_725249038f35aab4717e6cb1
declaration: isomorphism
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.sectionsWithSupportIso Hartshorne.sectionsWithSupport Hartshorne.isLocalizedModule_sectionsWithSupport_basicOpen Hartshorne.isLocalizedModule_sectionsWithSupport_stalk Hartshorne.isLocalizing_sectionsWithSupport
---

# Affine sections with support

Let $A$ be Noetherian, $X = \operatorname{Spec} A$, $Z = V(a)$, and $F=\widetilde{M}$. The subsheaf
of sections of $F$ supported on $Z$ is canonically isomorphic to the tilde
sheaf of

$\Gamma _a(M) = \{m | a^n m = 0 \text{for} \text{some} n > 0\}$.

The statement includes the identification on stalks and on affine basic opens,
so it can serve later as the degree-zero local-cohomology construction.

## Depends on

- [Support of a quasi-coherent module](module-sheaf-support.md)
- [Stalks of an associated affine module](../modules-and-quasicoherent/affine-tilde/tilde-localization.md)
- [Algebraic local cohomology as derived torsion](../../cohomology/affine-cohomology/local-cohomology-derived-torsion.md)

## Proof depends on

- [Affine quasi-coherent equivalence](../modules-and-quasicoherent/affine-quasicoherent-equivalence.md)
- [Quasi-coherent pushforward](../modules-and-quasicoherent/qcqs-pushforward-quasicoherent.md)
- Affine clearing of denominators.

## Sources

- [Hartshorne II.5, Exercise 5.6(d) (p.124)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
