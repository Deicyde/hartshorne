---
article_id: af_f0e771c2f787c06e6215db4a
declaration: def
origin: cited
mathlib: true
mathlib_declaration: KaehlerDifferential.linearMapEquivDerivation
mathlib_file: Mathlib/RingTheory/Kaehler/Basic.lean
---

# The universal module of Kähler differentials

For a ring map $A \to B$, the canonical derivation

$d:B\longrightarrow\Omega_{B/A}$

is universal: for every $B$-module $M$, composition with $d$ gives a natural
linear equivalence

$\operatorname{Hom}_B(\Omega_{B/A},M)\cong\operatorname{Der}_A(B,M)$.

The differential module can also be described as $I/I^2$, where
$I$ is the kernel of multiplication $B\otimes_A B\to B$. This is
the diagonal description in Hartshorne's Proposition II.8.1A.

## Depends on

No project-local prerequisites.

## Sources

- [Hartshorne II.8, definitions on p. 172 and background Proposition 8.1A on p. 173](../../../../sources/hartshorne-ii-8.md)
