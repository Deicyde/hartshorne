---
article_id: af_bf35d9766bdb3d61d239bfe0
declaration: theorem
origin: cited
lean: AlgebraicGeometry.Scheme.exists_mono_moduleSheafDual_tensor_pushforward
statement: formalized
proof: formalized
---

# The denominator ideal of a birational line bundle

For the line bundle $L$ in a projective birational morphism $f : Z \to X$, view
$f_*L$ as a coherent fractional ideal in the common function field. If $A$ is
ample on the quasi-projective target, then for some $n > 0$ the twist
$A^{-n} \otimes f_*L$ embeds as a coherent ideal of $\mathcal{O}_X$.

## Depends on

- [Ample invertible sheaves](../linear-systems-ampleness/ample-invertible-sheaf.md)
- [Birational varieties have isomorphic function fields](../../../rational-maps/birational-function-fields.md)
- [Coherence of projective pushforward](../../projective-sheaves/projective-pushforward-coherent.md)
- [The invertible sheaf associated to a Cartier divisor](../../divisors/cartier-picard/cartier-divisor-associated-sheaf.md)

## Proof depends on

- [Global regular functions inside the function field](../../../morphisms/global-functions/global-regular-in-function-field.md)
- [Functoriality of function fields](../../../morphisms/function-field-functorial.md)
- [Cartier classes and the Picard group of an integral scheme](../../divisors/cartier-picard/divisor-class-picard-equivalence.md)
- Common denominators for a finite set of local generators.
- [Generation by global sections](../../projective-sheaves/globally-generated-module-sheaf.md)
  applied to a sufficiently positive twist of the denominator ideal.

## Sources

- [Hartshorne II.7, proof of Theorem 7.17, Step 4 (p.167)](../../../../sources/hartshorne-ii-7.md#blowups)
