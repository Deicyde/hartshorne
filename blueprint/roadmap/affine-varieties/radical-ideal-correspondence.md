---
article_id: af_e7ef021d07d027ea3714eae3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isIrreducible_iff_isPrime
---

# Algebraic sets and radical ideals

$Y \mapsto I(Y)$ and $\mathfrak{a} \mapsto Z(\mathfrak{a} )$ are mutually inverse, inclusion-reversing bijections
between the algebraic sets in $\mathbb{A} ^{n}$ and the radical ideals of $A$. Under this
bijection an algebraic set is irreducible if and only if its ideal is prime
(Corollary 1.4).

The bijection is formal from the Galois connection once the Nullstellensatz
supplies $I(Z(\mathfrak{a} )) = \sqrt{\mathfrak{a}}$. The irreducible-iff-prime half is the part with real
content and is the main result of this node: if $fg \in I(Y)$ then $Y$ is covered
by the two closed sets $Y \cap Z(f)$ and $Y \cap Z(g)$, so irreducibility forces one
of them to be all of $Y$.

Two consequences Hartshorne draws immediately are worth proving here because
later sections cite them: $\mathbb{A} ^{n}$ is irreducible, and every maximal ideal of $A$ is
$(x_{1} - a_{1}, \ldots , x_{n} - a_{n})$ for a unique point $(a_{1},\ldots ,a_{n})$.

## Depends on

- [The vanishing ideal](vanishing-ideal.md)
- [Hilbert's Nullstellensatz](nullstellensatz.md)
- [Affine and quasi-affine varieties](affine-variety.md)

## Sources

- [Hartshorne I.1, Corollary 1.4 with Examples 1.4.1 and 1.4.4 (p. 4)](../../sources/hartshorne.md#i1)
