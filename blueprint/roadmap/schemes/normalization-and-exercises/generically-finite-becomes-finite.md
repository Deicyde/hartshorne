---
article_id: af_2217eb9deafef6d890207798
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_dense_isFinite_morphismRestrict_of_genericallyFinite
---

# A generically finite morphism is finite over a dense open

Let $f : X \to Y$ be dominant, generically finite, finite type, with $X$ and $Y$ integral. There is a dense open $U \subseteq Y$ such that $f^{-1}(U) \to U$ is finite.

Here, as in Hartshorne, $f$ is generically finite when the fibre $f^{-1}(\eta)$ over the generic point $\eta$ of $Y$ is a finite set, and finite type means locally of finite type and quasi-compact.

The generic fiber condition makes $K(X)$ a finite extension of $K(Y)$. Choose finitely many integral equations after clearing denominators on an affine neighbourhood of the generic point, then shrink the target so the relevant source becomes affine and module finite.

## Depends on

- [The function field of an integral scheme](function-field-integral-scheme.md)
- [Morphisms of finite type](../first-properties/finite-type.md)
- [Finite morphisms](../first-properties/finite-morphism.md)

## Proof depends on

- Finite generation plus algebraicity implies a finite field extension; denominator clearing and affine shrinking.

## Sources

- [Hartshorne II.3 (later-used-exercises)](../../../sources/hartshorne-ii-3.md#later-used-exercises)

