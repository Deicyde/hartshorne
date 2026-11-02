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

$\alpha:\operatorname{Hom}(X,Y)\longrightarrow\operatorname{Hom}_{k\text{-alg}}(A(Y),\mathcal O(X))$ (Proposition 3.5),

where the left side is morphisms of varieties and the right side is $k$-algebra
homomorphisms.

Forward, a morphism pulls regular functions back, and $\mathcal{O} (Y) \cong A(Y)$ by Theorem
3.2. Backward, given $h : A(Y) \to \mathcal{O} (X)$, write $Y \subseteq \mathbb{A} ^{n}$, let $\overline{x}_{i}$ be the image of
$x_{i}$ in $A(Y)$, and set $\psi (P) = (h(\overline{x}_{1})(P), \ldots , h(\overline{x}_{n})(P))$. Its image lands in $Y$
because any $f \in I(Y)$ satisfies $f(\psi (P)) = h(f)(P) = 0$, and it is a morphism by
Lemma 3.6.

Naturality in both arguments is not part of this node. Hartshorne does not spell
it out, and the equivalence of categories does need the bijection to be natural
rather than a family of bijections, so it is proved
[there](affine-variety-equivalence.md), where the functors it is natural in
exist. Proving it here would mean stating those functors here.

## The bijection does not need [Theorem I.3.2(a)](global-regular-eq-coordinate-ring.md)

Hartshorne phrases the forward map as "pull back regular functions, then apply
$\mathcal{O} (Y) \cong A(Y)$", which reads as a dependency on part (a). It is not one.
Precomposing with the map $A(Y) \to \mathcal{O} (Y)$ gives the same map, and nothing in
either round trip needs it to be injective or surjective. The statement is also
free of the algebraically closed hypothesis, which (a) does need.

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
