---
article_id: af_9c4d4fb277a1234fb29a6c06
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.finiteType_iff_exists_affine_cover
---

# Morphisms of finite type

A morphism $f : X \to Y$ of schemes is of finite type if there exists a covering of $Y$ by
open affine subsets $V_i = \operatorname{Spec} B_i$ such that for each $i$, $f^{-1}(V_i)$ can be
covered by a finite number of open affine subsets $U_{ij} = \operatorname{Spec} A_{ij}$, where each
$A_{ij}$ is a finitely generated $B_i$-algebra.

## Depends on

- [Morphisms locally of finite type](locally-finite-type.md)
- [Quasi-compact morphisms](quasi-compact-morphism.md)

## Proof depends on

- [The affine-target criterion for local finite type](locally-finite-type-affine-target-criterion.md)
- Exercise 3.3(a), identifying Hartshorne's finite-cover clause with quasi-compactness.

## Sources

- [Hartshorne II.3 (finite-type-and-finite-morphisms)](../../../sources/hartshorne-ii-3.md#finite-type-and-finite-morphisms)
