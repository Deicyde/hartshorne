---
article_id: af_cf06bb1e31416a59c82e0a20
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_gradedPrimeFiltration
---

# Graded prime filtrations

Let $S$ be a Noetherian integer-graded ring and let $M$ be a finitely
generated integer-graded $S$-module. There is a finite increasing filtration
by homogeneous submodules

$$0=M_0\subseteq M_1\subseteq\cdots\subseteq M_t=M$$

such that every quotient $M_i/M_{i-1}$ is isomorphic as a graded module
to $(S/\mathfrak p_i)(l_i)$ for a homogeneous prime ideal
$\mathfrak p_i$ and an integer $l_i$.

Choose a maximal homogeneous submodule admitting such a filtration. If
it is not all of $M$, choose in the quotient a nonzero homogeneous element
with maximal annihilator. That annihilator is prime, so adjoining the
cyclic submodule extends the filtration, a contradiction.

## Depends on

- [Integer-graded submodules and quotients](graded-submodules-and-quotients.md)
- [Homogeneous annihilators and cyclic modules](graded-annihilator.md)

## Sources

- [Hartshorne I.7, existence clause of Proposition 7.4 (pp. 50–51)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
