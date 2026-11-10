---
article_id: af_865c9bf4c43ed692cc5dfe48
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Surface.IsAlgebraicallyContractible Hartshorne.Surface.AlgebraicContraction Hartshorne.Surface.AlgebraicContraction.birationalOver Hartshorne.Surface.AlgebraicContraction.partialIso
---

# Contractible curves

Let $Y$ be an irreducible curve on a nonsingular projective surface $X$ over
$k$.  Call $Y$ algebraically contractible if there are a variety $X_0$ over
$k$, a point $P$ of $X_0$, and a birational morphism $f:X\to X_0$ such that

$f(Y)=\{P\}$ and $f:X-Y \to X_0-P$

is an isomorphism.  The target need not be projective, and it is allowed to be
singular.

Algebraic contractibility is stronger than contractibility in the category of
complex analytic spaces: an analytic contraction, as given by Grauert's
theorem, can exist when no algebraic one does.

## Depends on

- [Surfaces and effective curves](../../intersection-theory/foundations/surface-curve-convention.md)
- [Birational maps](../../../rational-maps/birational-map.md)

## Sources

- [Hartshorne V.5, Remark 5.7.2, p.417](../../../../sources/hartshorne-v-5.md)
