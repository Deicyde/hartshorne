---
article_id: af_fa39a1fdc6ec6ce41e14cdd1
declaration: instance
origin: background
mathlib: true
mathlib_declaration: KaehlerDifferential.isLocalizedModule_map
mathlib_file: Mathlib/RingTheory/Etale/Kaehler.lean
---

# Localization of Kähler differentials

Let $T$ be a localization of an $R$-algebra $S$ at a submonoid $M$.  The
canonical map

$\Omega_{S/ R} \to \Omega_{T/ R}$

exhibits the target as the localization of the source at $M$.  Equivalently,
there is a canonical $T$-linear equivalence

$T\otimes_S\Omega_{S/R}\cong\Omega_{T/R}$.

The isomorphism follows from the universal property of
differentials and the formal étaleness of localization.

## Depends on

- [The universal module of Kähler differentials](kahler-differential-universal.md)

## Sources

- [Hartshorne II.8, localization clause of background Proposition 8.2A, printed p. 173](../../../../sources/hartshorne-ii-8.md)
