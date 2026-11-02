---
article_id: af_587d2163b44f5944c3c8c7be
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_affine_open_cover_iff_forall_isAffineOpen_preimage
---

# The affine-morphism criterion

A morphism $f : X \to Y$ is affine when there exists an affine open cover
$\{V_i\}$ of $Y$ such that every $f^{-1}(V_i)$ is affine. Exercise 5.17(a) proves
that this is equivalent to requiring $f^{-1}(V)$ affine for every affine open
$V \subseteq Y$. Every affine morphism is quasi-compact and separated, and every
finite morphism is affine.

The three permanence statements follow from the affine criterion.

## Depends on

- [Affine cover criterion](../foundational-properties/affine-cover-criterion.md)
- [Quasi-compact morphisms](../first-properties/quasi-compact-morphism.md)
- [Finite morphisms](../first-properties/finite-morphism.md)

## Proof depends on

- Affineness is local on the target, and affine morphisms are separated.

## Sources

- [Hartshorne II.5, Exercise 5.17(a,b) (p.128)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
