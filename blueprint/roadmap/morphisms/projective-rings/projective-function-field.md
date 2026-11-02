---
article_id: af_2083bac423a66fdd008a0280
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projFunctionFieldEquivGraded
---

# The function field of a projective variety

Let $Y$ be a projective variety meeting a standard affine chart $U_i$.
Hartshorne's Theorem I.3.4(c) gives

$$K(Y)\cong S(Y)_{((0))}.$$

Restricting to the affine chart preserves the function field. The affine
coordinate ring is $A(Y_i)\cong S(Y)_{(x_i)}$, and its fraction field
is $S(Y)_{((0))}$. Uniqueness of a fraction field joins these identifications.

The ring $S(Y)$ is a domain because $J(Y)$ is prime. The class of $x_i$
is nonzero because the chart meets $Y$.

There is also a direct description: a degree-zero homogeneous fraction
$g/h$ defines a rational function $P\mapsto g(P)/h(P)$ on the open set
where $h$ is nonzero. Equal degrees make this independent of the chosen
homogeneous coordinates. Equal fractions give the same rational function
by cross multiplication. Conversely, every rational function is locally
such a fraction, giving the same field identification.

## Depends on

- [The function field of an arbitrary variety](../function-field-abstract.md)
- [The function field is functorial for dominant morphisms](../function-field-functorial.md)
- [Graded localization](graded-localization.md)
- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Proof depends on

- [The function field is the fraction field](../function-field-is-fraction-field.md)
- [The charts are isomorphisms of varieties](chart-isomorphism.md)
- [Varieties are covered by affine pieces](../../projective-varieties/affine-cover.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(c) (pp. 18-19)](../../../sources/hartshorne.md#i3)
