---
article_id: af_b50502a7621858814a6db862
declaration: definition
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.gradedModuleTwist
---

# Integer-graded module twists

Let $M=\bigoplus_{d\in\mathbb Z}M_d$ be a graded module over an
integer-graded ring. For $l\in\mathbb Z$, its *twist* is the same module
with grading

$$M(l)_d=M_{d+l}.$$

The scalar action remains compatible with the new grading. The identity
twist is $M(0)=M$, and successive twists satisfy $M(l)(m)=M(l+m)$.
A graded isomorphism is a module isomorphism carrying each homogeneous
piece to the piece of the same degree.

If a homogeneous element has degree $l$, the cyclic module it generates
is isomorphic as a graded module to a quotient of $S$ twisted by $-l$.

## Depends on

- [The integer grading on a polynomial ring](integer-polynomial-grading.md)

## Sources

- [Hartshorne I.7, definition of the twisted module before Proposition 7.4 (p. 50)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
