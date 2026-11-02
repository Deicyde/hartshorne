---
article_id: af_8994ed8cb0812948eff0e5f2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_const_eq_globalRegular Hartshorne.eval_eq_zero_of_eval_eq_zero_on_open Hartshorne.inter_inter_nonempty Hartshorne.mk_cross_eq Hartshorne.mk_X_pow_ne_zero
---

# The global regular functions of a projective variety

For a projective variety $Y$ over an algebraically closed field $k$,
Hartshorne's Theorem I.3.4(a) says that every global regular function is
constant:

$$\mathcal O(Y)=k.$$

On each standard affine chart meeting $Y$, write $f=g_i/x_i^{N_i}$.
The [chart description](chart-reading.md) gives these homogeneous fractions.
Choose one chart $i_0$ and regard $t=g_{i_0}/x_{i_0}^{N_{i_0}}$ as a
fraction-field element. On overlaps,

$$g_{i_0}x_i^{N_i}=g_i x_{i_0}^{N_{i_0}}$$

in $S(Y)$: the homogeneous polynomials agree on a nonempty open subset
and hence everywhere by the identity principle. Thus one element $t$
satisfies every chart's denominator condition.

For $N\geq\sum_iN_i$, the [degree bound](degree-bound.md) gives
$tS(Y)_N\subseteq S(Y)_N$. The piece $S(Y)_N$ is nonzero and
finite-dimensional. The [stable-subspace theorem](stable-subspace.md)
makes $t$ integral over $k$, hence constant because $k$ is algebraically
closed. Then $f$ is constant on the chosen chart and, by the identity
principle, on all of $Y$.

## Depends on

- [The ring of regular functions](../ring-of-regular-functions.md)
- [Global regular functions inside the function field](../global-functions/global-regular-in-function-field.md)
- [An element stabilising a finite-dimensional subspace is integral](stable-subspace.md)
- [Reading a global regular function on a chart](chart-reading.md)
- [The degree bound](degree-bound.md)
- [Graded localization](graded-localization.md)
- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Proof depends on

- [The coordinate ring is the ring of regular functions](../global-regular-eq-coordinate-ring.md)
- [The charts are isomorphisms of varieties](chart-isomorphism.md)
- [Varieties are covered by affine pieces](../../projective-varieties/affine-cover.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(a) (pp. 18-19)](../../../sources/hartshorne.md#i3)
