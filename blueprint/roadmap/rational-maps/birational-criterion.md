---
article_id: af_bee9a975db6a53592b5a0819
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.birational_criterion
---

# The birational criterion

For varieties $X$ and $Y$ in Hartshorne's four concrete classes, carrying the
affine-open-basis and separatedness witnesses used by the §4 category, the
following are equivalent (Corollary 4.5):

1. $X$ and $Y$ are birationally equivalent;
2. there are open subsets $U \subseteq X$ and $V \subseteq Y$ with $U$ isomorphic to $V$;
3. $K(X) \cong K(Y)$ as $k$-algebras.

Clause 2 is the one that makes birational equivalence concrete: birational
varieties are not merely related by a formal correspondence, they are literally
the same variety away from a proper closed subset of each.

## The proof

$(1) \Longrightarrow (2)$ is the only step with content. Let $\varphi : X \dashrightarrow Y$ and $\psi : Y \dashrightarrow X$ be
mutually inverse, represented by $\langle U, \varphi \rangle$ and $\langle V, \psi \rangle$. Then $\psi \circ \varphi$ is
represented by $\langle \varphi ^{-1}(V), \psi \circ \varphi \rangle$ and equals $\mathrm{id}_X$ as a rational map, so it is
the identity on $\varphi ^{-1}(V)$; symmetrically $\varphi \circ \psi$ is the identity on $\psi ^{-1}(U)$.
Taking $\varphi ^{-1}(\psi ^{-1}(U)) \subseteq X$ and $\psi ^{-1}(\varphi ^{-1}(V)) \subseteq Y$ gives two open sets carried to
each other by $\varphi$ and $\psi$, mutually inverse there, hence isomorphic.

$(2) \Longrightarrow (3)$ is the definition of the function field: an open subset of a variety
has the same rational functions as the variety, since a rational function is
already only defined on an open set.

$(3) \Longrightarrow (1)$ is [Theorem 4.4](rational-map-function-field.md), the isomorphism
and its inverse giving mutually inverse dominant rational maps.

## Depends on

- [Birational varieties have isomorphic open subsets](birational-open-subsets.md)
- [Birational varieties have isomorphic function fields](birational-function-fields.md)

## Sources

- [Hartshorne I.4, Corollary 4.5 (p. 26)](../../sources/hartshorne.md#i4)
