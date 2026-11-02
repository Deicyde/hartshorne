---
article_id: af_00f356814aa13851cf5257ea
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.coordinateRingEquivGlobalRegular
---

# The coordinate ring is the ring of regular functions

For an affine variety $Y$, the map $\alpha : A(Y) \to \mathcal{O} (Y)$ sending a polynomial class
to the function it defines is an isomorphism of $k$-algebras (Theorem 3.2(a)).

This is the part of Theorem 3.2 the rest of §3 actually consumes: [Proposition I.3.5](hom-affine-bijection.md) is stated as a bijection $\operatorname{Hom}(X,Y)\cong\operatorname{Hom}_{k\text{-alg}}(A(Y),\mathcal O(X))$, and it is
$\alpha$ that lets the two sides be compared at all.

Injectivity is the correspondence of §1 pushed through the quotient: a
polynomial defining the zero function on $Y$ lies in $I(Y)$.

## Surjectivity, by a different route than Hartshorne's

Hartshorne derives surjectivity from part (c), writing
$\mathcal O(Y)=\bigcap_P\mathcal O_P=\bigcap_{\mathfrak m}A(Y)_{\mathfrak m}=A(Y)$ inside $K(Y)$. That needs the local rings,
their identification with localisations of $A(Y)$, and one fact he takes from
outside: that a domain is the intersection of its localisations at all maximal
ideals.

None of it is needed. Given a regular $f$, take the *ideal of denominators*

$\mathfrak a=\{a\in A(Y):af\text{ is a polynomial function}\}$.

Regularity at $P$ writes $f = g/h$ near $P$ with $h(P) \ne 0$. Then $h\cdot f$ and $g$
are both regular on all of $Y$ and agree on that neighbourhood, so the identity
principle makes them agree everywhere: $\overline{h} \in \mathfrak{a}$, and $\overline{h} \notin \mathfrak{m} _P$. So $\mathfrak{a}$ lies in no
maximal ideal, since every maximal ideal is some $\mathfrak{m} _P$ by part (b), and hence
$\mathfrak{a} = A(Y)$. Then $1 \in \mathfrak{a}$, which says exactly that $f$ is a polynomial function.

The two ingredients, the identity principle and part (b), were already
available, so this node costs nothing beyond assembling them. It also breaks the
dependency of (a) on (c), which was the reason (a) had been sitting behind the
still-open dimension clause.

Irreducibility of $Y$ enters exactly once, to make the identity principle
available.

## Depends on

- [The ring of regular functions](ring-of-regular-functions.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Proof depends on

- [Points and maximal ideals](points-eq-maximal-ideals.md)
- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, Theorem 3.2(a) (p. 17)](../../sources/hartshorne.md#i3)
