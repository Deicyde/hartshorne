---
article_id: af_99a287d25bb1d1989e451bf8
declaration: definition
origin: cited
statement: formalized
lean: Hartshorne.RatMap Hartshorne.RatMapRep.IsDominant
---

# Rational maps

A *rational map* $\varphi : X \dashrightarrow Y$ between varieties is an equivalence class of pairs
$\langle U, \varphi _U\rangle$ with $U \subseteq X$ nonempty open and $\varphi _U : U \to Y$ a morphism, where
$\langle U, \varphi _U\rangle \sim \langle V, \varphi _V\rangle$ when $\varphi _U$ and $\varphi _V$ agree on $U \cap V$. The rational map is
*dominant* if for some, equivalently every, representative the image of $\varphi _U$ is
dense in $Y$.

A rational map is not a map of sets from $X$ to $Y$. It has no value at a point
outside the open sets where it is represented, and the section never pretends
otherwise.

## Why this needs [Lemma I.4.1](morphism-agreement.md)

Reflexivity and symmetry are immediate; transitivity is not. If $\varphi _U = \varphi _V$ on
$U \cap V$ and $\varphi _V = \varphi _W$ on $V \cap W$, all that is directly available is agreement
on $U \cap V \cap W$, which is a nonempty open subset of $U \cap W$ rather than all of
it. $U \cap W$ is itself a variety and $U \cap V \cap W$ is nonempty because $X$ is
irreducible, so [Lemma 4.1](morphism-agreement.md) upgrades the agreement to all
of $U \cap W$.

The same pattern already appeared in §3 for the function field, where rational
*functions* are equivalence classes of pairs $\langle U, f\rangle$. There the identity
principle for regular functions was enough, because the target was $k$. Here the
target is an arbitrary variety and the identity principle is not enough; [Lemma I.4.1](morphism-agreement.md) is what replaces it.

That "for some, equivalently every" in the definition of dominant needs less:
two representatives agree on the overlap of their domains, which is dense in
each, so each image lies in the closure of the other and the two closures agree.
No separatedness is used.

Composition is described separately in
[Composition of dominant rational maps](rational-map-composition.md).

## Depends on

- [Morphisms agreeing on an open set](morphism-agreement.md)
- [Morphisms](../morphisms/morphism.md)
- [Varieties](../morphisms/variety.md)

## Sources

- [Hartshorne I.4, definition of rational map (p. 24)](../../sources/hartshorne.md#i4)
