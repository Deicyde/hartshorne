---
article_id: af_efc666120dfb5881de675ab4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.RationalMapFunctionField.bijective_functionFieldAlgHom_of_hasAffineOpenBasis Hartshorne.RationalMapFunctionField.functionFieldFunctor_isEquivalence
---

# Rational maps and function fields

For varieties $X$ and $Y$ in Hartshorne's four concrete classes, which have
an affine-open basis by [Proposition I.4.3](affine-base.md), there is a bijection between

- dominant rational maps $X \dashrightarrow Y$, and
- $k$-algebra homomorphisms $K(Y) \to K(X)$,

and this correspondence is an arrow-reversing equivalence between the category
of such varieties with dominant rational maps and the category of finitely
generated field extensions of $k$ (Theorem 4.4).

This is the section's main result and the birational counterpart of Corollary
3.8. There, the coordinate ring determined an affine variety up to isomorphism;
here, the function field determines *any* variety up to birational equivalence.

## The map in one direction

Given a dominant $\varphi$ represented by $\langle U, \varphi _U\rangle$ and a rational function on $Y$
represented by $\langle V, f\rangle$, dominance makes $\varphi _U(U)$ dense in $Y$, so $\varphi _U^{-1}(V)$ is
a nonempty open subset of $X$ and $f \circ \varphi _U$ is regular on it. That is a rational
function on $X$, and the assignment is a $k$-algebra homomorphism
$K(Y) \to K(X)$.

## The inverse

Given $\theta : K(Y) \to K(X)$, a dominant rational map is built back. By
[Proposition 4.3](affine-base.md) $Y$ is covered by affine open sets and
$K(Y) = K(V)$ for any of them, so $Y$ may be assumed affine. Take generators
$y_{1},\ldots ,y_n$ of $A(Y)$ as a $k$-algebra. Their images $\theta (y_{i})$ are rational
functions on $X$, so all are regular on some common nonempty open $U \subseteq X$, and
$\theta$ restricts to an injective $k$-algebra map $A(Y) \to \mathcal{O} (U)$. [Proposition I.3.5](../morphisms/hom-affine-bijection.md)
turns that into a morphism $U \to Y$, hence a rational map $X \dashrightarrow Y$, and injectivity
of $\theta$ makes it dominant. The two constructions are mutually inverse.

## Why the categories match up

Two closure statements finish the equivalence. Every $K(Y)$ is a finitely
generated field extension of $k$: pass to an affine open subset, where [Theorem I.3.2(d)](../morphisms/function-field-is-fraction-field.md) identifies $K(Y)$ with the fraction field of $A(Y)$. Conversely every
finitely generated $K/k$ is some $K(Y)$: take generators $y_{1},\ldots ,y_n \in K$, let $B$
be the $k$-subalgebra they generate, note $B$ is a quotient of a polynomial ring
and a domain, so $B \cong A(Y)$ for a variety $Y$ in $\mathbb{A} ^{n}$ by the realization
half of [Corollary I.3.8](../morphisms/affine-variety-equivalence.md), and then $K \cong K(Y)$.

## Depends on

- [Composition of dominant rational maps](rational-map-composition.md)
- [The function field of an arbitrary variety](../morphisms/function-field-abstract.md)
- [Open affine sets are a base for the topology](affine-base.md)

## Proof depends on

- [Morphisms into an affine variety](../morphisms/hom-affine-bijection.md)
- [The function field is functorial for dominant morphisms](../morphisms/function-field-functorial.md)
- [The function field is the fraction field](../morphisms/function-field-is-fraction-field.md)
- [Equivalence with finitely generated domains](../morphisms/affine-variety-equivalence.md)
- [The coordinate ring is the ring of regular functions](../morphisms/global-regular-eq-coordinate-ring.md)
- [Global regular functions are the intersection of the local rings](../morphisms/global-functions/global-regular-intersection-local-rings.md)

## Sources

- [Hartshorne I.4, Theorem 4.4 (pp. 25-26)](../../sources/hartshorne.md#i4)
