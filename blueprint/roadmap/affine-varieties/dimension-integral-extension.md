---
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.strictMono_primeSpectrum_comap Hartshorne.ringKrullDim_le_of_isIntegral Hartshorne.le_ringKrullDim_of_isIntegral Hartshorne.ringKrullDim_eq_of_isIntegral
---

# Krull dimension is invariant under integral extensions

Let `R → S` be an injective integral ring extension. Then `dim S = dim R`.

This is the engine behind Theorem 1.8A, and Hartshorne never states it: it is
inside the Matsumura and Atiyah–Macdonald citations. It is split out here
because both halves are self-contained and because the result is worth
upstreaming on its own.

The two inequalities are asymmetric in difficulty and in hypotheses.

`dim S ≤ dim R` is incomparability: two comparable primes of `S` with the same
contraction to `R` are equal, so contraction is a *strictly monotone map*
`Spec S → Spec R` and dimension is monotone along strictly monotone maps. No
injectivity needed.

`dim R ≤ dim S` is lying over plus going up, and it is not a map. A chain in
`Spec R` is *lifted*: lying over produces a prime of `S` above the bottom of the
chain, and going up walks it upward one step at a time. Injectivity enters
exactly at lying over, and it is not decoration — `S → S/𝔪` is integral for
every maximal ideal `𝔪`, and it takes any dimension to `0`.

## Mathlib boundary

Mathlib has both halves as ingredients and neither as a conclusion.
`Ideal.IsIntegral.comap_lt_comap` is incomparability in the form needed;
`Ideal.exists_ltSeries_of_hasGoingUp` is the chain induction, and
`Algebra.HasGoingUp.of_isIntegral` supplies its hypothesis. What is missing is
the passage to `ringKrullDim`, in both directions.

## Depends on

- [Dimension of a topological space and of a ring](dimension.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)
