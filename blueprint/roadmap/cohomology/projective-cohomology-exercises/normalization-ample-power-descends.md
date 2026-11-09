---
article_id: af_059d05b4cdfaf27a571796f5
declaration: theorem
origin: cited
---

# A very ample sheaf descends from a curve normalization

Let $X$ be a proper integral one-dimensional scheme over an algebraically
closed field $k$, let $\nu :\widetilde{X}\to X$ be its normalization, and let
$L$ be very ample on $\widetilde{X}$. There is an effective divisor
$D=\sum P_i$ on $\widetilde{X}$ with $L\cong \mathcal{O}_{\widetilde{X}}(D)$
such that each $P_i$ maps to a nonsingular point of $X$. Consequently there is
an invertible sheaf $L_{0}$ on $X$ such that $\nu ^*L_{0}\cong L$.

The sheaf $L_{0}$ is obtained by descending $D$ to $X$ along $\nu$, which is
an isomorphism near the images of the $P_i$.

## Depends on

- [Construction of the normalization](../../schemes/normalization-and-exercises/normalization-construction.md)
- [Cartier divisors and their associated sheaves](../../schemes/divisors/cartier-picard/cartier-divisor-associated-sheaf.md)
- [Effective Cartier divisors and locally principal subschemes](../../schemes/divisors/cartier-picard/effective-cartier-closed-subscheme.md)
- [Relative twisting sheaves and very ampleness](../../schemes/projective-sheaves/relative-twisting-and-very-ample.md)

## Proof depends on

- [Finiteness of normalization over a field](../../schemes/normalization-and-exercises/normalization-finite-type-field.md)
- [The normalization is an isomorphism over a normal open](../../schemes/normalization-and-exercises/normalization-iso-over-normal-open.md)
- [The normalization is normal and integral](../../schemes/normalization-and-exercises/normalization-normal-integral.md)
- [Characterizations of discrete valuation rings](../../nonsingular-curves/dvr-characterizations.md)
- [Projective iff proper and very ample](../../schemes/projective-sheaves/projective-iff-proper-very-ample.md)
- $\widetilde{X}$ is proper over $k$ (being finite over the proper $X$), normal of
  dimension one and hence nonsingular, and therefore a nonsingular projective
  variety, so Proposition II.7.7 applies to it.
- [Divisors of invertible-sheaf sections](../../schemes/projective-geometry/linear-systems-ampleness/divisor-of-invertible-section.md)
- [The dense nonsingular locus](../../schemes/differentials/scheme-differentials/dense-nonsingular-locus.md)
- Regular one-dimensional local rings are normal (Theorem I.6.2A above), and a
  proper closed subset of an integral curve is finite, so the normal locus of
  $X$ is open with finite complement.
- A very ample sheaf over an infinite field has a global section vanishing at
  none of finitely many prescribed closed points (a hyperplane section avoids
  any finite set of points), so, $L$ itself being very ample, a divisor $D$ in
  $|L|$ can be chosen away from the finite preimage of the singular locus.
- A Cartier divisor supported over the open set where $\nu$ is an isomorphism
  descends to $X$, and pulling the descended divisor back along $\nu$ is
  compatible with the associated invertible sheaves.

## Sources

- [Hartshorne III, Exercise 5.8(b), p.232](../../../sources/hartshorne-iii-5.md#adopted-exercises-pp230233)
