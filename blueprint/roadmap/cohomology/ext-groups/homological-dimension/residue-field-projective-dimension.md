---
article_id: af_903d71598a93080c404c0326
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.RegularLocal.projectiveDimension_residueField_eq_ringKrullDim Hartshorne.RegularLocal.projectiveDimension_residueField
---

# Projective dimension of the residue field

Let $(A,m,k)$ be a Noetherian regular local ring. Then

$pd_A(k)=\dim A$.

This equality is the sharpness clause in the regular-local global-dimension
theorem and is kept separate because later depth arguments use it as a
specific computation.

Let $d=\dim A$ and let $x_1,\ldots,x_d$ generate $m$. Since $A$ is
Cohen–Macaulay and $\dim A/(x_1,\ldots,x_d)=0=d-d$, the sequence
$x_1,\ldots,x_d$ is regular. The quotient of a local ring by a regular sequence
of length $d$ in its maximal ideal has projective dimension exactly $d$, and
here that quotient is $A/m=k$.

## Depends on

- [Regular local rings](../../../nonsingular-varieties/regular-local-rings.md)
- [Projective-dimension bounds detected by Ext](projective-dimension-ext-criterion.md)

## Proof depends on

- [Regular local rings are Cohen–Macaulay](../../../schemes/differentials/local-complete-intersections/regular-local-implies-cohen-macaulay.md)
- [Regular sequences and Cohen–Macaulay quotients](../../../schemes/differentials/local-complete-intersections/cohen-macaulay-regular-sequence-quotient.md)
- [A regular local ring is an integral domain](../../../nonsingular-varieties/regular-local-ring-domain.md)
- [Regular hypersurface quotients of a regular local ring](../../../schemes/differentials/canonical-bertini/regular-hypersurface-local-criterion.md)
- The quotient of a local ring by a regular sequence of length $d$ in its
  maximal ideal has projective dimension $d$.

## Sources

- [Hartshorne III.6, Proposition 6.11A(b), printed p.237](../../../../sources/hartshorne-iii-6.md#quoted-homological-algebra-printed-pp236237)
- Matsumura [2], Theorem 42, p.131, as cited by Hartshorne.
