---
article_id: af_94ada4945067ebd4c954f5cc
declaration: theorem
origin: background
mathlib: true
mathlib_declaration: Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange
mathlib_file: Mathlib/RingTheory/Smooth/Local.lean
---

# The Jacobian criterion for formally smooth local algebras

Let $R$ be a commutative ring and let $S$ be a local $R$-algebra with maximal
ideal $\mathfrak m$. Let $P$ be a formally smooth $R$-algebra whose module
$\Omega_{P/R}$ is finite and free, and let $P \to S$ be a surjective
homomorphism of $R$-algebras with finitely generated kernel $I$. Let $K$ be a
field with an $S$-algebra structure whose structure map kills $\mathfrak m$, so
that $K$ is an extension of the residue field of $S$. Then
$S$ is formally smooth over $R$ if and only if the $K$-linear map

$$K \otimes_P I \longrightarrow K \otimes_P \Omega_{P/R}, \qquad
a \otimes f \longmapsto a \otimes df,$$

is injective.

## Depends on

- [The universal module of Kähler differentials](../../../schemes/differentials/kaehler-differentials/kahler-differential-universal.md)

## Proof depends on

No additional project-local results.

## Sources

- [Prerequisite for the comparison of Hartshorne's III.10 definition of smoothness, p.268, with the adopted predicate](../../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
