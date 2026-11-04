---
article_id: af_60f933bd73afed54cd8907e2
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.homEquivAlgHom
---

# Morphisms into an affine variety

Let $X$ be any variety and $Y$ an affine variety. Then there is a natural
bijection

$\alpha:\operatorname{Hom}(X,Y)\longrightarrow\operatorname{Hom}_{k\text{-alg}}(A(Y),\mathcal O(X))$
(Hartshorne's Proposition I.3.5),

where the left side is morphisms of varieties and the right side is $k$-algebra
homomorphisms.

In one direction, a morphism pulls regular functions back, using
[the coordinate-ring isomorphism](global-regular-eq-coordinate-ring.md).
In the other direction, given $h : A(Y) \to \mathcal{O} (X)$, write $Y \subseteq \mathbb{A} ^{n}$, let $\overline{x}_{i}$ be the image of
$x_{i}$ in $A(Y)$, and set $\psi (P) = (h(\overline{x}_{1})(P), \ldots , h(\overline{x}_{n})(P))$. Its image lands in $Y$
because any $f \in I(Y)$ satisfies $f(\psi (P)) = h(f)(P) = 0$, and it is a morphism by
[Hartshorne's Lemma I.3.6](morphism-to-affine-criterion.md).

The compatibility of these bijections with morphisms in both arguments is
developed in the
[equivalence between affine varieties and finitely generated domains](affine-variety-equivalence.md).

## A direct construction of the bijection

Hartshorne constructs the forward map by pulling regular functions back
and applying $\mathcal{O} (Y) \cong A(Y)$. The same map can be defined
directly by precomposing with $A(Y) \to \mathcal{O} (Y)$.
The verification of the two inverse constructions does not require this
last map to be injective or surjective. This direct argument also applies
without the algebraically closed hypothesis used in Theorem I.3.2(a).

The identity carrying the whole proof is $f(\psi (x)) = h(\overline{f})(x)$ for every
polynomial $f$, where $\psi (x)_{i} = h(\overline{x}_{i})(x)$. Both sides are $k$-algebra maps out of
the polynomial ring in $f$ and agree on the variables, so they agree. Landing in
$Y$ and being a morphism both fall out of it: the first because $\overline{f} = 0$ for
$f \in I(Y)$, the second by [Lemma I.3.6](morphism-to-affine-criterion.md), since the coordinates of $\psi$ are the values
of $h$ and so regular by construction.


## Depends on

- [Morphisms](morphism.md)
- [The ring of regular functions](ring-of-regular-functions.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Proof depends on

- [The coordinate ring is the ring of regular functions](global-regular-eq-coordinate-ring.md)
- [Criterion for a morphism into an affine variety](morphism-to-affine-criterion.md)

## Sources

- [Hartshorne I.3, Proposition 3.5 (p. 19)](../../sources/hartshorne.md#i3)
