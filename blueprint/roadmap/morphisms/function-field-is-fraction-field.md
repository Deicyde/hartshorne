---
article_id: af_dd1cbde9cdbfd8ab2b1cd243
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isFractionRing_functionField Hartshorne.exists_dim_eq_trdeg_functionField
---

# The function field is the fraction field

For an affine variety $Y$, the function field $K(Y)$ is the fraction
field of $A(Y)$ and

$$\operatorname{trdeg}_k K(Y)=\dim Y.$$

This is Hartshorne's Theorem I.3.2(d). A nonzero coordinate-ring element
is nonzero on a nonempty open subset, where its reciprocal is regular.
Every rational function is locally a quotient $g/h$ of polynomial
functions, so every element of $K(Y)$ is a fraction of elements of $A(Y)$.
The identity principle extends the local equality $hz=g$ to equality of
rational functions. The coordinate-ring map is injective because a
polynomial function with zero rational class vanishes everywhere.

Finally, $\dim Y=\dim A(Y)$ and the dimension of a finitely generated
domain equals the transcendence degree of its fraction field.

## Depends on

- [The function field](function-field.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)
- [Dimension is the dimension of the coordinate ring](../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [Dimension of a finitely generated domain](../affine-varieties/dim-fg-domain.md)

## Sources

- [Hartshorne I.3, Theorem 3.2(d) (p. 17)](../../sources/hartshorne.md#i3)
