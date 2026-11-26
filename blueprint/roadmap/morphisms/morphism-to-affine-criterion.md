# Criterion for a morphism into an affine variety

Let $X$ be a variety and let $Y\subseteq\mathbb A^n$ be an affine
variety. A set map $\psi:X\to Y$ is a morphism if and only if every
coordinate function $x_i\circ\psi$ is regular on $X$.

This is Hartshorne's Lemma I.3.6. Necessity follows from the definition.
Conversely, regularity of the coordinates makes $f\circ\psi$ regular
for every polynomial $f$, proving continuity through closed zero sets.
Regular functions on $Y$ are locally quotients of polynomials, so their
pullbacks are regular by division and locality.

The same argument allows a quasi-affine target, since it does not require
closedness of $Y$.

## Depends on

- [Morphisms](morphism.md)
- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)
- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, Lemma 3.6 (p. 20)](../../sources/hartshorne.md#i3)
