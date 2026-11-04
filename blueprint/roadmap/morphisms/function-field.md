---
article_id: af_f960b52328c9616ca4870018
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.FunctionField
---

# The function field

The *function field* $K(Y)$ of a variety $Y$ consists of equivalence classes of
pairs $(U, f)$ with $U$ a nonempty open subset and $f$ regular on $U$, where
$(U, f)$ and $(V, g)$ are identified when $f = g$ on $U \cap V$. Its elements are
the *rational functions* on $Y$.

$K(Y)$ is a field. Addition and multiplication are defined because $Y$ is
irreducible, so any two nonempty open sets meet; inverses exist because a nonzero
$(U, f)$ restricts to $V = U \setminus Z(f)$, which is nonempty and on which $1/f$ is
regular. Irreducibility guarantees the nonempty intersections and restrictions
needed in this construction.

$K(Y)$ is defined without reference to $\mathcal{O} _P$: both are equivalence
classes of pairs $(U, f)$, differing only in whether $U$ is required to contain a
fixed point. The comparison between them is
[the canonical injections into the function field](function-field-injections.md).

## The same construction for an arbitrary variety

The same construction applies to an arbitrary variety, including the
projective varieties of
[Hartshorne's Theorem I.3.4(c)](projective-rings/projective-function-field.md).
See [the general construction](function-field-abstract.md).

## Depends on

- [Varieties](variety.md)
- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)
- [Regular functions on a quasi-projective variety](regular-function-quasi-projective.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, definition of $K(Y)$ (p. 16)](../../sources/hartshorne.md#i3)
