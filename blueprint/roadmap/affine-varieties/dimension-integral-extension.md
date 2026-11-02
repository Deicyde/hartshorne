---
article_id: af_edfd5d5cec98a8f47ed0cf78
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.strictMono_primeSpectrum_comap Hartshorne.ringKrullDim_le_of_isIntegral Hartshorne.le_ringKrullDim_of_isIntegral Hartshorne.ringKrullDim_eq_of_isIntegral
---

# Krull dimension is invariant under integral extensions

Let $R \to S$ be an injective integral ring extension. Then $\dim S = \dim R$.

This is the engine behind Theorem 1.8A, and Hartshorne never states it: it is
inside the Matsumura and Atiyah–Macdonald citations. It is split out here
because the two inequalities use different prime-chain arguments.

The two inequalities are asymmetric in difficulty and in hypotheses.

$\dim S \le \dim R$ is incomparability: two comparable primes of $S$ with the same
contraction to $R$ are equal, so contraction is a *strictly monotone map*
$\operatorname{Spec} S \to \operatorname{Spec} R$ and dimension is monotone along strictly monotone maps. No
injectivity needed.

$\dim R \le \dim S$ is lying over plus going up, and it is not a map. A chain in
$\operatorname{Spec} R$ is *lifted*: lying over produces a prime of $S$ above the bottom of the
chain, and going up walks it upward one step at a time. Injectivity enters
exactly at lying over, and it is not decoration — $S \to S/\mathfrak{m}$ is integral for
every maximal ideal $\mathfrak{m}$, and it takes any dimension to $0$.

## Depends on

- [Dimension of a topological space and of a ring](dimension.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)
