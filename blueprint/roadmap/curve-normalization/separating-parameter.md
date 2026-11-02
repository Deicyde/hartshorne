---
article_id: af_cdd991fa7124477bed654f2a
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.exists_separatingParameter
---

# One-dimensional function fields have separating parameters

Let $K/k$ be an essentially finitely generated field extension of
transcendence degree one, with $k$ algebraically closed. There is a
transcendental element $t\in K$ such that $K/k(t)$ is finite and separable.

The separating-transcendence-basis theorem over the perfect field $k$
produces a basis of cardinality one. Its unique element generates $k(t)$,
over which $K$ is finite and separable. This refines Hartshorne's choice of
an arbitrary nonconstant parameter in the proof of Lemma I.6.5.

The same conclusion holds for $t^{-1}$, since $k(t^{-1}) = k(t)$. This gives the second normalization chart.

## Depends on

No project-local statement prerequisites.

## Proof depends on

- [Separably generated field extensions](../rational-maps/separably-generated.md)

## Sources

- [Hartshorne I.4, Theorem 4.8A (p. 27)](../../sources/hartshorne.md#i4)
- [Hartshorne I.6, one-dimensional function fields in the proof of Lemma 6.5 (p. 41)](../../sources/hartshorne.md#i6-normalization-and-finite-poles)
