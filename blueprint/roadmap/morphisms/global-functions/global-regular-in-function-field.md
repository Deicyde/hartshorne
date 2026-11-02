---
article_id: af_ee708c56a9d1c21e6fd3eca4
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.Variety.globalToFunctionField
---

# Global regular functions inside the function field

For a variety $X$, viewing a global regular function as a rational
function gives an injective ring homomorphism

$$\mathcal O(X)\hookrightarrow K(X).$$

The embedding commutes with pullback along dominant morphisms. On an
affine variety, the embedding from $A(X)$ into $K(X)$ agrees with the
composite through the identification $A(X)\cong\mathcal O(X)$.

A global regular function has domain all of $X$. Two such functions with
the same rational class agree on a nonempty open subset and hence
everywhere by the identity principle.

## Depends on

- [The function field of an arbitrary variety](../function-field-abstract.md)
- [The function field is functorial for dominant morphisms](../function-field-functorial.md)
- [The ring of regular functions](../ring-of-regular-functions.md)

## Proof depends on

- [The coordinate ring is the ring of regular functions](../global-regular-eq-coordinate-ring.md)
- [The function field is the fraction field](../function-field-is-fraction-field.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(a) (pp. 18-19)](../../../sources/hartshorne.md#i3)
