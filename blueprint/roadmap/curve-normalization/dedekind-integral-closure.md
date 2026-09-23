---
article_id: af_cdbb59a26819ffce4274f733
declaration: theorem
origin: background
source_units: [theorem-i-6-3a]
---

# Integral closures of Dedekind domains

Let `A` be an integrally closed Noetherian domain of Krull dimension one with
fraction field `K`, and let `L/K` be a finite field extension.  Then the
integral closure `B` of `A` in `L` is an integrally closed Noetherian domain of
Krull dimension one: a Dedekind domain in Hartshorne's sense.

This is Theorem 6.3A with no separability assumption.  The pinned Mathlib
already supplies, without separability, that `B` is a domain, is integrally
closed, is integral over `A`, and has fraction field `L`.  Krull--Akizuki gives
Noetherianity.  Integral extensions preserve dimension, so the source's exact
dimension-one conclusion should be retained in addition to Mathlib's
`IsDedekindDomain` class, which permits fields and records only dimension at
most one.

## Depends on

No project-local statement prerequisites.

## Proof depends on

- [The Krull--Akizuki theorem](krull-akizuki.md)
- [Krull dimension is invariant under integral extensions](../affine-varieties/dimension-integral-extension.md)

## Sources

- [Hartshorne I.6, Theorem 6.3A (p. 40)](../../sources/hartshorne.md#i6-integral-closure-theorem)
